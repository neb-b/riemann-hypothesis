module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BaseChangeTensorProduct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem ChartCover.exists_lift {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) :
    ∃ xF : Sp S ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = w.x ∧ xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  refine ⟨pullback.lift w.x (spMap (algebraMap c.F S)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  rw [w.x_over, spMap_comp_ring]
  rfl

theorem ChartCover.near (hS : Out.SecBaseChangeSt) {R A : Type} [CommRing R] [Algebra c.F R] [CommRing A]
    [Algebra c.F A] {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A} {s : Aˣ} {u : FrPt Xo c A}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (p : Sp S) (hp : xF p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam g) →
      ∃ (z : FrPt Xo c T) (a : A →ₐ[c.F] T), FrMap lam w z ∧ FrMap a u z := by
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c R j y₀ hj S xF h2 p hp
  refine ⟨g, hg, fun T _ _ lam hl => ?_⟩
  obtain ⟨ψ, hψ⟩ := hT T lam hl
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c S T lam w
  have hx : z.x = spMap ψ.toRingHom ≫ y₀.x := by
    rw [hz.1, ← h1, ← hj.2.1, ← Category.assoc, hψ, Category.assoc]
  obtain ⟨a, ⟨_, ha⟩, _⟩ := _root_.GlobalTheory.Frames.univFrame_classifies hS E H Dw l Xo c R A y₀ π X s u hu T z ψ hx
  exact ⟨z, a, hz, ha⟩

theorem ChartCover.cls_loc (hS : Out.SecBaseChangeSt) {R : Type} [CommRing R] [Algebra c.F R] {A : TRing c.F}
    {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A.R}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R} {s : (A.R)ˣ} {u : FrPt Xo c A.R}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (m : Ideal S) [hm : m.IsPrime]
    (hp : xF (⟨m, hm⟩ : PrimeSpectrum S) ∈ Set.range j) :
    ∃ cw : A.R →ₐ[c.F] Localization.AtPrime m,
      ChartCls (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m u cw ∧
      ChartLoc (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m A u := by
  obtain ⟨g, hg, hT⟩ := ChartCover.near hS hj hu w xF h1 h2 (⟨m, hm⟩ : PrimeSpectrum S) hp
  obtain ⟨z, a, hz, ha⟩ := hT (Localization.AtPrime m) (locM c.F m)
    (IsLocalization.map_units (Localization.AtPrime m) (⟨g, hg⟩ : m.primeCompl))
  refine ⟨a, ⟨z, hz, ha⟩, ?_⟩
  intro p φ y hy
  obtain ⟨yF, k1, k2⟩ := ChartCover.exists_lift y
  have e : spMap φ.toRingHom ≫ yF = xF := by
    apply pullback.hom_ext
    · rw [Category.assoc, k1, h1, hy.1]
    · rw [Category.assoc, k2, h2, spMap_comp_ring]
      congr 1
      exact φ.comp_algebraMap
  have hq : yF (spMap φ.toRingHom (⟨m, hm⟩ : PrimeSpectrum S)) ∈ Set.range j := by
    rw [← e] at hp
    exact hp
  obtain ⟨g', hg', hT'⟩ := ChartCover.near hS hj hu y yF k1 k2 _ hq
  obtain ⟨p', lam, hl, hlam⟩ := GlobalTheory.testRing_localizationAway c.F p g'
  obtain ⟨z', a', hz', ha'⟩ := hT' p'.R lam hl
  exact ⟨g', hg', p', lam, z', a', hlam, hz', ha'⟩

end

theorem chartCoverF_of_secBaseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartCoverF Xo c := by
  intro hS E _ _ _ H Dw l Xo c S _ _ w w' hw m hm
  obtain ⟨xF, h1, h2⟩ := ChartCover.exists_lift w
  obtain ⟨p, j, y₀, hj, hp⟩ := _root_.GlobalTheory.Frames.exists_openChart_testRing hS E H Dw l Xo c (xF (⟨m, hm.isPrime⟩ : PrimeSpectrum S))
  obtain ⟨A, π, X, s, u, hu⟩ := _root_.GlobalTheory.Frames.exists_univFrame_testRing hS E H Dw l Xo c p y₀
  obtain ⟨cw, hc, hl⟩ := ChartCover.cls_loc hS hj hu w xF h1 h2 m hp
  obtain ⟨cw', hc', hl'⟩ := ChartCover.cls_loc hS hj hu w' xF (h1.trans hw.symm) h2 m hp
  exact ⟨A, u, cw, cw', _root_.GlobalTheory.Frames.univFrame_classifies_unique hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hu,
    _root_.GlobalTheory.Frames.univFrame_borelPairs hS E H Dw l Xo c p A j y₀ π X s u hj hu, hc, hl, hc', hl'⟩

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOneAddSubOne
section
namespace GlobalTheory.MarkDet

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prod_sub_prod {ι : Type} (M : ℕ) (s : Finset ι) (I : ι → FractionalIdeal (𝓞 E)⁰ E)
    (y z : ι → RA F E) (hy : ∀ i, y i ∈ hat1 F (I i : Set E)) (hz : ∀ i, z i ∈ hat1 F (I i : Set E)) :
    ∃ w ∈ hat1 F ((∏ i ∈ s, I i : FractionalIdeal (𝓞 E)⁰ E) : Set E),
      ∏ i ∈ s, (y i + M • z i) - ∏ i ∈ s, y i = M • w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, zero_mem _, by simp⟩
  | insert a s ha ih =>
    obtain ⟨w, hw, e⟩ := ih
    have hp := prod_mem_adelicCompletionOfElementSet F s I y (fun i _ => hy i)
    have mul := (adelicCompletion_fractionalIdeal_properties F E).1 (I a) (∏ i ∈ s, I i)
    refine ⟨y a * w + z a * (∏ i ∈ s, y i + M • w), ?_, ?_⟩
    · rw [Finset.prod_insert ha]
      exact add_mem (mul _ (hy a) _ hw) (mul _ (hz a) _ (add_mem hp (nsmul_mem hw M)))
    · rw [Finset.prod_insert ha, Finset.prod_insert ha, sub_eq_iff_eq_add.1 e]
      simp only [nsmul_eq_mul]
      ring

theorem det_one_add_sub_one {n : ℕ} (M : ℕ) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, cI a ≠ 0)
    (K : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, K i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    ∃ w ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E), (1 + M • K).det - 1 = M • w := by
  have h1 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (RA F E)) i j ∈
      hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, mul_inv_cancel₀ (hc i), Algebra.TensorProduct.one_def]
      exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
    · rw [Matrix.one_apply_ne hij]
      exact zero_mem _
  have key : ∀ σ : Equiv.Perm (Fin n), ∃ w ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E),
      ∏ j, (1 + M • K) (σ j) j - ∏ j, (1 : Matrix (Fin n) (Fin n) (RA F E)) (σ j) j = M • w := by
    intro σ
    have := prod_sub_prod F M Finset.univ (fun j => cI (σ j) * (cI j)⁻¹)
      (fun j => (1 : Matrix (Fin n) (Fin n) (RA F E)) (σ j) j) (fun j => K (σ j) j)
      (fun j => h1 _ _) (fun j => h _ _)
    rw [Finset.prod_mul_distrib, Equiv.prod_comp σ cI, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i)] at this
    exact this
  choose w hw e using key
  refine ⟨∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • w σ, sum_mem fun σ _ => ?_, ?_⟩
  · rw [Units.smul_def]
    exact zsmul_mem (hw σ) _
  · have d1 : (1 : RA F E) = (1 : Matrix (Fin n) (Fin n) (RA F E)).det := Matrix.det_one.symm
    rw [d1, Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← smul_sub, e, Units.smul_def, Units.smul_def, smul_comm]

theorem det_sub_one_of_cong {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : ℕ) (hM : M ≠ 0)
    (G : Matrix (Fin n) (Fin n) (RA F E))
    (hg : ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ y ∈ hat F (L : Set (Fin n → E)), G *ᵥ z - z = M • y) :
    ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), G.det - 1 = M • w := by
  have hone : ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) = Set.range (algebraMap (𝓞 E) E) := by
    ext x
    exact FractionalIdeal.mem_one_iff _
  rw [← hone]
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key' : ∀ w, P *ᵥ w ∈ hat F (L : Set (Fin n → E)) ↔ ∀ a, w a ∈ hat1 F (cI a : Set E) := by
    intro w; rw [hP]; exact key w
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.mpr hM
  obtain ⟨m, hm⟩ : ∃ m : RA F E, m * (M : RA F E) = 1 :=
    ⟨algebraMap F (RA F E) (M : F)⁻¹, by
      rw [← map_natCast (algebraMap F (RA F E)) M, ← map_mul, inv_mul_cancel₀ hMF, map_one]⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) (RA F E), N = m • (G - 1) := ⟨_, rfl⟩
  have hGN : G = 1 + M • N := by
    rw [hN, ← Nat.cast_smul_eq_nsmul (RA F E), smul_smul, mul_comm, hm, one_smul, add_sub_cancel]
  have hNz : ∀ z ∈ hat F (L : Set (Fin n → E)), N *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
    intro z hz
    obtain ⟨y, hy, ey⟩ := hg z hz
    rw [hN, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ey,
      ← Nat.cast_smul_eq_nsmul (RA F E), smul_smul, hm, one_smul]
    exact hy
  obtain ⟨k, hk0⟩ : ∃ k : Matrix (Fin n) (Fin n) (RA F E), k = Q * N * P := ⟨_, rfl⟩
  have hPk : P * k = N * P := by
    simp only [hk0, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hkdet : (1 + M • k).det = G.det := by
    have h1 : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    have h2 : 1 + M • k = Q * G * P := by
      rw [hGN, hk0, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQP, Matrix.mul_smul, Matrix.smul_mul]
    rw [h2]
    simp only [Matrix.det_mul]
    linear_combination G.det * h1
  have hk : ∀ i j, k i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun x hx => ?_
    have h1 : P *ᵥ (Pi.single j ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x)) ∈
        hat F (L : Set (Fin n → E)) := by
      rw [key']
      intro a
      by_cases ha : a = j
      · subst ha
        rw [Pi.single_eq_same]
        exact one_tmul_mem_adelicCompletionOfElementSet F hx
      · rw [Pi.single_eq_of_ne ha]
        exact zero_mem _
    have h2 := hNz _ h1
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, key'] at h2
    have h3 := h2 i
    rwa [Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at h3
  rw [← hkdet]
  exact det_one_add_sub_one F M cI hc k hk

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

theorem gLat_eq_of_finCong {D : D7} {V : HSp D} {N : ℕ} {u : GA D V} (hu : FinCong V N u) :
    gLat V u = latHat V := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact PrincLevel.finCong_map hu y hy
  · intro hz
    refine ⟨_, PrincLevel.finCong_map (PrincLevel.finCong_inv hu) z hz, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]


end GlobalTheory.MarkDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpFourClauses
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

namespace GlobalTheory.ExpClauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))

theorem expUniq : ExpUniq e F := by
  intro i P P' hP hP' gam h hEF hM hA hrel z
  have hm : ∀ z, Matrix.mulVec (LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) z = h z :=
    fun z => LinearMap.toMatrix'_mulVec _ z
  have key := @GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E _ _ _ H Dw l Xo _ g _ F i P P' gam
    (LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) hP hP' hEF hM hA (fun a => by rw [hm]; exact hrel a)
  have := key.2.2 z
  rwa [hm] at this

theorem expLin : ExpLin e F := by
  intro i P hP m w vs cf v hvs hv
  exact (@GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E _ _ _ H Dw l Xo _ g _ F i P hP m vs w hvs cf v).2 hv

theorem expTan : ExpTan e F := by
  intro i P hP w v hv
  refine ⟨(@GlobalTheory.isDerivAt0_ex_isTanAt E _ _ _ H Dw l Xo _ g _ F i P hP).1 w v hv, fun j hj => ?_⟩
  refine (@GlobalTheory.isEigAt_iff_of_isDerivAt0 E _ _ _ H Dw l Xo c σ g e F i P hP w v (e j).1 hv).2 fun j' hj' => ?_
  by_cases hjj : j' = j
  · rw [hjj]
  · exact absurd (by rw [hj, Pi.single_eq_of_ne hjj]) hj'

theorem lieEig : LieEig e F := by
  intro i P hP τ v hv he
  obtain ⟨w, hw, -⟩ := (@GlobalTheory.isDerivAt0_ex_isTanAt E _ _ _ H Dw l Xo _ g _ F i P hP).2.2 v hv
  have hs := (@GlobalTheory.isEigAt_iff_of_isDerivAt0 E _ _ _ H Dw l Xo c σ g e F i P hP w v τ hw).1 he
  refine ⟨fun j => w (e.symm ⟨τ, j⟩), ?_⟩
  have hsum : (∑ j, w (e.symm ⟨τ, j⟩) • eb e τ j) = w := by
    funext k
    obtain ⟨⟨τ', m⟩, rfl⟩ := e.symm.surjective k
    by_cases hτ : τ' = τ
    · subst hτ
      exact sum_eb_apply e τ' (fun j => w (e.symm ⟨τ', j⟩)) m
    · have h0 : w (e.symm ⟨τ', m⟩) = 0 := by
        by_contra hne
        have := hs _ hne
        rw [Equiv.apply_symm_apply] at this
        exact hτ this
      rw [h0]
      simp [Finset.sum_apply, eb_apply, Sigma.mk.inj_iff, hτ]
  rw [hsum]
  exact hw

end GlobalTheory.ExpClauses

theorem GlobalTheory.exp_four_clauses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)), ExpUniq e F ∧ ExpLin e F ∧ ExpTan e F ∧ LieEig e F :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ e F =>
    ⟨GlobalTheory.ExpClauses.expUniq e F, GlobalTheory.ExpClauses.expLin e F, GlobalTheory.ExpClauses.expTan e F, GlobalTheory.ExpClauses.lieEig e F⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntFrExtOfGoodLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Exist

theorem exists_prime_mem_maximalIdeal_of_finite_residue (V : Type) [CommRing V] [IsLocalRing V]
    [Finite (IsLocalRing.ResidueField V)] : ∃ p : ℕ, p.Prime ∧ (p : V) ∈ IsLocalRing.maximalIdeal V := by
  obtain ⟨p, hp⟩ := CharP.exists (IsLocalRing.ResidueField V)
  refine ⟨p, CharP.char_is_prime (IsLocalRing.ResidueField V) p, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem intFrExt_of_good : PartI → N1ab → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → IntFrExt Xo c := by
  intro hP hN hB hT E _ _ _ H Dw l Xo c hpq hgood T io hfin x hx
  have : Finite (IsLocalRing.ResidueField T.V) := hfin
  obtain ⟨p, hp, hpm⟩ := exists_prime_mem_maximalIdeal_of_finite_residue T.V
  obtain ⟨O, _, β, Y, hPI, b, hb⟩ := _root_.GlobalTheory.exists_model_pushInvertible_under_cdvr hP hN E H Dw l Xo c hpq T io p hp hpm (hgood p hp)
  have hIF := _root_.GlobalTheory.intFrames_of_laws hB hT E H Dw l Xo c
  let _ := io.toAlgebra
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr) hT (fun _ => rfl) x hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨y, t, hbor⟩ := intFr_of_model hIF T io Y hPI b hb y₀
  refine ⟨T, RingHom.id _, 1, one_pos, fun z => by simp, hfin, y, ?_⟩
  have h1 : y.1.x = y₀.x := hbor.1
  have h2 : spMap (RingHom.id T.Fr) = 𝟙 _ := Spec.map_id _
  show y.1.x = _
  rw [h2, Category.id_comp, h1, h0]

end GlobalTheory.Exist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LinearIndependentOfIndepToC
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ReadingComparison

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
  ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {K L : Type} [Field K] [Field L] [Algebra K L] {σ : K →+* ℂ} {σ' : L →+* ℂ}
  {C W : Type} [AddCommGroup C] [Module K C] [AddCommGroup W] [Module ℂ W]

theorem bcMap_tmul (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) (t : L) (x : C) :
    BaseChangeTensorProduct.bcMap hσ f (t ⊗ₜ x) = σ' t • f x := rfl

theorem linearIndependent_of_indepToC {f : C →ₛₗ[σ] W} (hf : IndepToC f) {ι : Type} {b : ι → C}
    (hb : LinearIndependent K b) : LinearIndependent ℂ (fun i => f (b i)) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have e := s.equivFin
  have h1 := hf _ (fun i => b (e.symm i).1) (hb.comp (fun i => (e.symm i).1)
    (Subtype.val_injective.comp e.symm.injective))
  have h2 := h1.comp e e.injective
  convert h2 using 1
  funext i
  simp

theorem indepToC_bcMap_iff (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) :
    IndepToC (BaseChangeTensorProduct.bcMap hσ f) ↔ IndepToC f := by
  constructor
  · intro h n b hb
    have h1 := h n (fun i => (1 : L) ⊗ₜ[K] b i) (Module.Flat.linearIndependent_one_tmul hb)
    simpa only [bcMap_tmul, map_one, one_smul] using h1
  · intro h n b hb
    letI : Algebra K ℂ := σ.toAlgebra
    letI : Algebra L ℂ := σ'.toAlgebra
    haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq fun a => (hσ a).symm
    letI : Module K W := Module.compHom W σ
    haveI : IsScalarTower K ℂ W := ⟨fun a z w => by
      show (σ a * z) • w = σ a • z • w
      rw [mul_smul]⟩
    let g : C →ₗ[K] W :=
      { toFun := f, map_add' := map_add f, map_smul' := fun a x => f.map_smulₛₗ a x }
    let F : ℂ ⊗[K] C →ₗ[ℂ] W := g.liftBaseChange ℂ
    let e := Module.Basis.ofVectorSpace K C
    have hF : Function.Injective F := by
      refine LinearMap.injective_of_linearIndependent (Algebra.TensorProduct.basis ℂ e).span_eq ?_
      have h0 := linearIndependent_of_indepToC h e.linearIndependent
      have e1 : (F ∘ Algebra.TensorProduct.basis ℂ e) = fun i => f (e i) := by
        funext i
        simp only [Function.comp, Algebra.TensorProduct.basis_apply, F, LinearMap.liftBaseChange_one_tmul]
        rfl
      rw [e1]; exact h0
    let φ := TensorProduct.AlgebraTensorModule.cancelBaseChange K L ℂ ℂ C
    have h1 : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[L] b i) := Module.Flat.linearIndependent_one_tmul hb
    have h2 := h1.map' (F ∘ₗ φ.toLinearMap) (LinearMap.ker_eq_bot.2 (hF.comp φ.injective))
    have key : ∀ x : L ⊗[K] C, F (φ ((1 : ℂ) ⊗ₜ[L] x)) = BaseChangeTensorProduct.bcMap hσ f x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul t x =>
        rw [bcMap_tmul]
        simp only [φ, F, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.liftBaseChange_tmul]
        show (σ' t * 1) • f x = _
        rw [mul_one]
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
    have e2 : (fun i => BaseChangeTensorProduct.bcMap hσ f (b i)) = (F ∘ₗ φ.toLinearMap) ∘ fun i => (1 : ℂ) ⊗ₜ[L] b i :=
      funext fun i => (key (b i)).symm
    rw [e2]; exact h2

end General

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ)

end GlobalTheory.ReadingComparison
end
end

