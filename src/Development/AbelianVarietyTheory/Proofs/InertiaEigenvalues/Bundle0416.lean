module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0018
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescentFreeModuleCocycle
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open CategoryTheory

namespace GlobalTheory

theorem descent_free_cocycle : ∀ (A B D T : Type) [CommRing A] [CommRing B] [CommRing D] [CommRing T] [Algebra A B] (p q : B →+* D) (q₁₂ q₂₃ q₁₃ : D →+* T) (q₃ : B →+* T), (algebraMap A B).FaithfullyFlat → CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom p) (CommRingCat.ofHom q) → CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (p.comp (algebraMap A B))) (CommRingCat.ofHom q₃) (CommRingCat.ofHom q₁₂) → q₂₃.comp p = q₁₂.comp q → q₂₃.comp q = q₃ → q₁₃.comp p = q₁₂.comp p → q₁₃.comp q = q₃ → ∀ (d : ℕ) (ε : Matrix (Fin d) (Fin d) D), IsUnit ε → ε.map q₁₂ * ε.map q₂₃ = ε.map q₁₃ → ∀ N : Submodule A (Fin d → B), (∀ z, z ∈ N ↔ (fun i => p (z i)) = ε.mulVec fun i => q (z i)) → Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  intro A B D T _ _ _ _ _ p q q₁₂ q₂₃ q₁₃ q₃ hff hD hT h1 h2 h3 h4 d ε hε hcoc N hN
  haveI : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.1 hff
  have hTP := CommRingCat.isPushout_tensorProduct A B B
  let iso := hD.isoIsPushout _ _ hTP
  let e : D ≃+* B ⊗[A] B := iso.commRingCatIsoToRingEquiv
  let ψ : D →+* B ⊗[A] B := e.toRingHom
  have hψp : ∀ b, ψ (p b) = b ⊗ₜ[A] (1 : B) := fun b =>
    congr($(hD.inl_isoIsPushout_hom _ _ hTP).hom b)
  have hψq : ∀ b, ψ (q b) = (1 : B) ⊗ₜ[A] b := fun b =>
    congr($(hD.inr_isoIsPushout_hom _ _ hTP).hom b)
  let L : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)
  let R : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
    (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))
  let M : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  let c3 : B →+* B ⊗[A] (B ⊗[A] B) :=
    (R.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom
  have w : CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom c3 =
      CommRingCat.ofHom (p.comp (algebraMap A B)) ≫
        CommRingCat.ofHom (S := B ⊗[A] (B ⊗[A] B)) (L.toRingHom.comp ψ) := by
    ext a
    change c3 (algebraMap A B a) = L (ψ (p (algebraMap A B a)))
    rw [hψp]
    exact ((R.comp Algebra.TensorProduct.includeRight).commutes a).trans
      ((L.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).commutes a).symm
  let Φ := hT.desc _ _ w
  let φ : T →+* B ⊗[A] (B ⊗[A] B) := Φ.hom
  have hφ3 : ∀ b, φ (q₃ b) = c3 b := fun b => congr($(hT.inl_desc _ _ w).hom b)
  have hφ12 : ∀ x, φ (q₁₂ x) = L (ψ x) := fun x => congr($(hT.inr_desc _ _ w).hom x)
  have hext : ∀ {W : CommRingCat} (f g : CommRingCat.of D ⟶ W), (∀ b, f (p b) = g (p b)) →
      (∀ b, f (q b) = g (q b)) → f = g := fun f g hp hq =>
    hD.hom_ext (by ext b; exact hp b) (by ext b; exact hq b)
  have hφ23 : ∀ x, φ (q₂₃ x) = R (ψ x) := by
    have key := hext (CommRingCat.ofHom q₂₃ ≫ Φ)
      (CommRingCat.ofHom (S := B ⊗[A] (B ⊗[A] B)) (R.toRingHom.comp ψ)) ?_ ?_
    · intro x; exact congr($(key).hom x)
    · intro b
      change φ (q₂₃ (p b)) = R (ψ (p b))
      rw [show q₂₃ (p b) = q₁₂ (q b) from congr($h1 b), hφ12, hψq, hψp]
      simp [L, R]
    · intro b
      change φ (q₂₃ (q b)) = R (ψ (q b))
      rw [show q₂₃ (q b) = q₃ b from congr($h2 b), hφ3, hψq]
      simp [c3, R]
  have hφ13 : ∀ x, φ (q₁₃ x) = M (ψ x) := by
    have key := hext (CommRingCat.ofHom q₁₃ ≫ Φ)
      (CommRingCat.ofHom (S := B ⊗[A] (B ⊗[A] B)) (M.toRingHom.comp ψ)) ?_ ?_
    · intro x; exact congr($(key).hom x)
    · intro b
      change φ (q₁₃ (p b)) = M (ψ (p b))
      rw [show q₁₃ (p b) = q₁₂ (p b) from congr($h3 b), hφ12, hψp]
      simp [L, M]
    · intro b
      change φ (q₁₃ (q b)) = M (ψ (q b))
      rw [show q₁₃ (q b) = q₃ b from congr($h4 b), hφ3, hψq]
      simp [c3, R, M]
  let ε' : Matrix (Fin d) (Fin d) (B ⊗[A] B) := ε.map ψ
  have hε' : IsUnit ε' := hε.map ψ.mapMatrix
  have hcoc' : ε'.map L * ε'.map R = ε'.map M := by
    have key := congrArg φ.mapMatrix hcoc
    rw [map_mul] at key
    have e12 : φ.mapMatrix (ε.map q₁₂) = ε'.map L := by
      ext i j; simp [ε', hφ12]
    have e23 : φ.mapMatrix (ε.map q₂₃) = ε'.map R := by
      ext i j; simp [ε', hφ23]
    have e13 : φ.mapMatrix (ε.map q₁₃) = ε'.map M := by
      ext i j; simp [ε', hφ13]
    rw [e12, e23, e13] at key
    exact key
  have hN' : ∀ z, z ∈ N ↔ (fun i => z i ⊗ₜ[A] (1 : B)) = ε'.mulVec fun i => (1 : B) ⊗ₜ[A] z i := by
    intro z
    rw [hN z]
    have hv : (ψ ∘ fun i => q (z i)) = fun i => (1 : B) ⊗ₜ[A] z i := funext fun k => hψq _
    have hmv : ∀ i, ψ ((ε.mulVec fun i => q (z i)) i) = (ε'.mulVec fun i => (1 : B) ⊗ₜ[A] z i) i := by
      intro i; rw [RingHom.map_mulVec, hv]
    constructor
    · intro h; funext i
      rw [← hmv i, ← h, hψp]
    · intro h; funext i
      apply e.injective
      change ψ (p (z i)) = ψ _
      rw [hmv i, hψp]
      exact congrFun h i
  exact GlobalTheory.T.faithfullyFlat_descent_free_module_cocycle A B d ε' hε' hcoc' N hN'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Eps0UnramFrob
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem eps0_unram_frob : ∀ (D : D7) (i : D.ntw.Tw) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.ntw.l i) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) A v → (∀ σ ∈ Ine (F := D.host.E) A, eps0 D.ntw i σ = 1) ∧ ∀ σ : Gen.GE D.nd, IsFrob (F := D.host.E) A (normV v) σ → ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ) := by
  intro D i v hv A hA
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
  · have h1 : cycZ D.host.E D.nd.Om (D.ntw.l i) σ = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq hv hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
      simp
    unfold eps0
    rw [MonoidHom.comp_apply, h1, map_one]
  · have h1 := cycZ_of_isFrob (l := D.ntw.l i) hv hA hσ
    show algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i)
      ((cycZ D.host.E D.nd.Om (D.ntw.l i) σ : ℤ_[D.ntw.l i]ˣ) : ℤ_[D.ntw.l i]) = _
    rw [h1, map_natCast]

end GlobalTheory.TripleGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfStabilizerTrivial
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open scoped Pointwise

noncomputable section

namespace GlobalTheory.TypePlace

theorem exists_place {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (c : E →+* PadicAlgCl l) :
    ∃ v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ v.asIdeal ∧ ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1 :=
  _root_.GlobalTheory.IntegralNormSmallIdeal.exists_place_of_embedding c

theorem eq_of_stabilizer_trivial {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (a b : E →+* PadicAlgCl l) (P : Ideal (𝓞 E)) (ha : ∀ x : 𝓞 E, x ∈ P ↔ ‖a (x : E)‖ < 1)
    (hb : ∀ x : 𝓞 E, x ∈ P ↔ ‖b (x : E)‖ < 1) (hP : ∀ σ : E ≃ₐ[ℚ] E, σ • P = P → σ = 1) : a = b := by
  letI : Algebra E (PadicAlgCl l) := a.toAlgebra
  haveI : IsScalarTower ℚ E (PadicAlgCl l) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let φ : E →ₐ[ℚ] PadicAlgCl l := b.toRatAlgHom
  let σ : E ≃ₐ[ℚ] E := φ.restrictNormal' E
  have hσ : ∀ y, a (σ y) = b y := fun y => φ.restrictNormal_commutes E y
  have h1 : σ⁻¹ • P = P := by
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, ha, hb]
    have e : ((σ • y : 𝓞 E) : E) = σ (y : E) := rfl
    rw [e, hσ]
  have h2 : σ = 1 := inv_eq_one.1 (hP _ h1)
  ext x
  rw [← hσ, h2]
  rfl

theorem conj_ne_one {R : Ranks} (H : Host R) : H.conj ≠ 1 := by
  intro h
  have h1 : H.galE H.conj = R.cc := H.galE_conjE
  rw [h, H.galE_one] at h1
  have h2 : (1 : ℤˣ) = -1 := congrArg (fun g : R.GG => g.1.2) h1
  exact absurd h2 (by decide)

theorem type_prime_places : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 = 1 ∧ ∀ w', IsConjPl D.host w w' → w' ≠ w) ∧ ∀ a b : D.host.E →+* Om (D.nd.l i), (∀ x : 𝓞 D.host.E, ‖a x‖ < 1 ↔ ‖b x‖ < 1) → a = b := by
  intro D i k hk
  have hs : (placesOver D.host.E (D.nd.l i)).ncard = finrank ℚ D.host.E := by
    rw [hk]; exact D.nd.g_split k
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  refine ⟨fun w hw => ⟨(GlobalTheory.TypeDegOne.degree_one D i k hk).2 w hw, fun w' hc he => ?_⟩, fun a b hab => ?_⟩
  · subst he
    have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.nd.l i) Fact.out hs w' hw).2.2
    refine conj_ne_one D.host (inv_eq_one.1 (hP _ ?_))
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    exact (hc y (D.host.conj • y) rfl).symm
  · obtain ⟨v, hv, ha⟩ := exists_place a
    have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.nd.l i) Fact.out hs v hv).2.2
    exact eq_of_stabilizer_trivial a b v.asIdeal ha (fun x => (ha x).trans (hab x)) hP

end GlobalTheory.TypePlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLetterOfHodgeJump
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.JumpVec

theorem exists_letter_of_jump : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ a : ℤ, IsJumpV ((D.loc l).PD K) T.ρ τ a → ∃ d ∈ Di (HW l) h T i, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ a ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∉ FilAt ((D.loc l).PD K) T τ (a + 1) := by
  intro D HW l _ K s LL h T hC i ζ τ hPt a hJ
  obtain ⟨-, hemb, ι, hComp⟩ := (GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hPt
  obtain ⟨-, -, -, hc, hc0⟩ := GlobalTheory.NL.Points.points D HW l K s LL h
  have hC3 := (GlobalTheory.NL.CompD.component_tied (D.locT l) K LL T hc hc0 hC τ ι hComp.2.2 _ hemb).2.2.1
  have hlt : FildR ((D.loc l).PD K) T.ρ τ (a + 1) < FildR ((D.loc l).PD K) T.ρ τ a :=
    lt_of_le_of_ne (GlobalTheory.DeRhamCompare.FildR_succ_le _ _ τ a) hJ
  obtain ⟨w, hwa, hwa1⟩ := SetLike.exists_of_lt hlt
  obtain ⟨d, hd, hdw⟩ := hC3 w hwa.1
  refine ⟨d, hd, ?_, ?_⟩
  · have : ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d =
        w + (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by abel
    rw [this]
    exact Submodule.add_mem_sup hwa hdw
  · intro hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
    have hdis := GlobalTheory.Per.FilLetUnram.iSupIndep_DdRE ((D.loc l).PD K) T.ρ τ
    have hD : w - y ∈ DdRE ((D.loc l).PD K) T.ρ τ := Submodule.sub_mem _ hwa.1 hy.1
    have hS : w - y ∈ ⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ' := by
      have : w - y = z - (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by
        rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hz hdw
    have h0 : w - y = 0 := Submodule.disjoint_def.1 hdis _ hD hS
    have : w = y := sub_eq_zero.1 h0
    exact hwa1 (this ▸ hy)

end GlobalTheory.NL.JumpVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureAdicCompletion
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.CDelta

variable {l : ℕ} [hl : Fact l.Prime] {L Q : Type} [CommRing L] [CommRing Q] {i : L →+* Q} {J : Ideal L}


omit hl in
theorem smul_top_eq (n : ℕ) : ((J.map i) ^ n • ⊤ : Submodule Q Q) = (J ^ n).map i := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_pow]


omit hl in
theorem eq_of_forall (hc : IsCompl i J) {u v : Q} (h : ∀ n, u - v ∈ (J ^ n).map i) : u = v := by
  refine sub_eq_zero.1 (hc.complete.toIsHausdorff.haus (u - v) fun n => ?_)
  rw [SModEq.sub_mem, sub_zero, smul_top_eq]; exact h n

omit hl in
theorem mem_succ {x : Q} {n : ℕ} (h : x ∈ (J ^ (n + 1)).map i) : x ∈ (J ^ n).map i :=
  Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) h

theorem key (hc : IsCompl i J) (hlJ : (l : L) ∈ J) (D : Delta l L) {x : Q} {a b : L} {n : ℕ}
    (ha : x - i a ∈ (J ^ (n + 1)).map i) (hb : x - i b ∈ (J ^ (n + 1)).map i) :
    i (D.δ a) - i (D.δ b) ∈ (J ^ n).map i := by
  have hab : a - b ∈ J ^ (n + 1) := hc.ker _ _ (by
    have := sub_mem hb ha
    rw [map_sub]; convert this using 1; ring)
  have h := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l L D J hlJ n b (a - b) hab
  rw [add_sub_cancel] at h
  rw [← map_sub]; exact Ideal.mem_map_of_mem _ h

theorem exists_lim (hc : IsCompl i J) (hlJ : (l : L) ∈ J) (D : Delta l L) (x : Q) :
    ∃ z : Q, ∀ (n : ℕ) (a : L), x - i a ∈ (J ^ (n + 1)).map i → z - i (D.δ a) ∈ (J ^ n).map i := by
  choose ap hap using hc.surj x
  obtain ⟨z, hz⟩ := hc.complete.toIsPrecomplete.prec (f := fun n => i (D.δ (ap (n + 1)))) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_top_eq]
    exact key hc hlJ D (hap (m + 1)) (Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) (hap (n + 1)))
  refine ⟨z, fun n a ha => ?_⟩
  have h1 := hz n
  rw [SModEq.sub_mem, smul_top_eq] at h1
  have h2 := key hc hlJ D (hap (n + 1)) ha
  have := sub_mem h2 h1
  convert this using 1; ring

end GlobalTheory.BSP.CDelta


open GlobalTheory.BSP.CDelta in
theorem GlobalTheory.BSP.exists_delta_completion : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q]
    (i : L →+* Q) (J : Ideal L), IsCompl i J → (l : L) ∈ J → ∀ D : Delta l L, ∃ D' : Delta l Q, IsδMap D D' i := by
  intro l _ L _ Q _ i J hc hlJ D
  choose d hd using exists_lim hc hlJ D
  have sep : ∀ u v : W2 l Q, (∀ n, W2.map (Ideal.Quotient.mk ((J ^ n).map i)) u =
      W2.map (Ideal.Quotient.mk ((J ^ n).map i)) v) → u = v := by
    intro u v h
    have h1 : ∀ n, Ideal.Quotient.mk ((J ^ n).map i) u.fst = Ideal.Quotient.mk ((J ^ n).map i) v.fst :=
      fun n => congrArg W2.fst (h n)
    have h2 : ∀ n, Ideal.Quotient.mk ((J ^ n).map i) u.snd = Ideal.Quotient.mk ((J ^ n).map i) v.snd :=
      fun n => congrArg W2.snd (h n)
    exact W2.ext (eq_of_forall hc fun n => Ideal.Quotient.eq.1 (h1 n))
      (eq_of_forall hc fun n => Ideal.Quotient.eq.1 (h2 n))
  have ap : ∀ (x : Q) (n : ℕ) (a : L), x - i a ∈ (J ^ (n + 1)).map i →
      W2.map (Ideal.Quotient.mk ((J ^ n).map i)) (⟨x, d x⟩ : W2 l Q) =
        W2.map ((Ideal.Quotient.mk ((J ^ n).map i)).comp i) (deltaSectionToWittLengthTwo D a) := by
    intro x n a ha
    have h1 : Ideal.Quotient.mk ((J ^ n).map i) x = Ideal.Quotient.mk ((J ^ n).map i) (i a) :=
      Ideal.Quotient.eq.2 (mem_succ ha)
    have h2 : Ideal.Quotient.mk ((J ^ n).map i) (d x) = Ideal.Quotient.mk ((J ^ n).map i) (i (D.δ a)) :=
      Ideal.Quotient.eq.2 (hd x n a ha)
    exact W2.ext h1 h2
  let s : Q →+* W2 l Q :=
    { toFun := fun x => ⟨x, d x⟩
      map_one' := sep _ _ fun n => by
        rw [ap 1 n 1 (by simp), map_one, map_one, map_one]
      map_zero' := sep _ _ fun n => by
        rw [ap 0 n 0 (by simp), map_zero, map_zero, map_zero]
      map_add' := fun x y => sep _ _ fun n => by
        obtain ⟨a, ha⟩ := hc.surj x (n + 1)
        obtain ⟨b, hb⟩ := hc.surj y (n + 1)
        have hab : x + y - i (a + b) ∈ (J ^ (n + 1)).map i := by
          rw [map_add (f := _)]; convert add_mem ha hb using 1; ring
        show W2.map _ (⟨x + y, d (x + y)⟩ : W2 l Q) = W2.map _ ((⟨x, d x⟩ : W2 l Q) + ⟨y, d y⟩)
        rw [ap _ n _ hab, map_add (W2.map (Ideal.Quotient.mk _)), ap x n a ha, ap y n b hb, map_add (deltaSectionToWittLengthTwo D),
          map_add]
      map_mul' := fun x y => sep _ _ fun n => by
        obtain ⟨a, ha⟩ := hc.surj x (n + 1)
        obtain ⟨b, hb⟩ := hc.surj y (n + 1)
        have hab : x * y - i (a * b) ∈ (J ^ (n + 1)).map i := by
          have : x * y - i (a * b) = y * (x - i a) + i a * (y - i b) := by rw [map_mul]; ring
          rw [this]; exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
        show W2.map _ (⟨x * y, d (x * y)⟩ : W2 l Q) = W2.map _ ((⟨x, d x⟩ : W2 l Q) * ⟨y, d y⟩)
        rw [ap _ n _ hab, map_mul (W2.map (Ideal.Quotient.mk _)), ap x n a ha, ap y n b hb, map_mul (deltaSectionToWittLengthTwo D),
          map_mul] }
  refine ⟨deltaStructureOfWittLengthTwoSection s fun _ => rfl, fun a => ?_⟩
  show i (D.δ a) = d (i a)
  exact (eq_of_forall hc fun n => hd (i a) n a (by simp)).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisMovesFlatByUnitRoot
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem rootT_mul' {l : ℕ} [Fact l.Prime] (a b : Per.Fl l) (n : ℕ) :
    GlobalTheory.MemLoc.rootT (a * b) n = GlobalTheory.MemLoc.rootT a n * GlobalTheory.MemLoc.rootT b n := by
  unfold GlobalTheory.MemLoc.rootT
  rw [← map_mul]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

theorem rootT_succ_pow' {l : ℕ} [Fact l.Prime] (a : Per.Fl l) (n : ℕ) :
    GlobalTheory.MemLoc.rootT a (n + 1) ^ l = GlobalTheory.MemLoc.rootT a n := by
  unfold GlobalTheory.MemLoc.rootT
  rw [Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]

theorem galois_moves_flat_by_unit_root : ∀ (l : ℕ) [Fact l.Prime], (∀ (x : ℂ_[l]) (m : ℕ), 0 < m → x ^ m = 1 → ∃ z : Om l, (z : ℂ_[l]) = x) → ∀ (K : FinExt l) (bk : BK K) (e : OCb l), e.untilt = 1 → ∃ g : ↥(GK K), Per.σF (g : GQ l) bk.flat = e * bk.flat := by
  intro l _ hroots K bk e he
  obtain ⟨hπ, hπu⟩ := GlobalTheory.BSP.BK.prime_unif l K bk
  obtain ⟨halg, hfix⟩ := GlobalTheory.BSP.rootT_flat_alg_and_fix l K bk
  choose y hy using halg
  have hc : ∀ n : ℕ, ∃ c : Om l, (c : ℂ_[l]) = ((GlobalTheory.MemLoc.rootT e n : OC l) : ℂ_[l]) := by
    intro n
    refine hroots _ (l ^ n) (pow_pos (Fact.out : l.Prime).pos n) ?_
    have h := congrArg (fun x : OC l => (x : ℂ_[l])) (GlobalTheory.MemLoc.rootT_pow_eq_untilt e n)
    simpa [he] using h
  choose c hc using hc
  have hcoe : ∀ x : Om l, (x : ℂ_[l]) = algebraMap (Om l) ℂ_[l] x := fun _ => rfl
  have hinj : Function.Injective (fun x : Om l => (x : ℂ_[l])) := (algebraMap (Om l) ℂ_[l]).injective
  have hy0 : y 0 = (((bk.str.symm (Ideal.Quotient.mk _ (X : bk.S)) : ↥(OL K)) : ↥K.1) : Om l) := by
    apply hinj
    beta_reduce
    rw [← hy 0, ← coe_intToOC, hπu]
    rfl
  have hc0 : c 0 = 1 := by
    apply hinj
    beta_reduce
    rw [hc 0, hcoe, map_one]
    show ((PreTilt.untilt e : OC l) : ℂ_[l]) = 1
    rw [he]
    rfl
  have hys : ∀ n, y (n + 1) ^ l = y n := by
    intro n
    apply hinj
    show ((y (n + 1) ^ l : Om l) : ℂ_[l]) = (y n : ℂ_[l])
    rw [hcoe, map_pow, ← hcoe, ← hy, ← hy, ← SubmonoidClass.coe_pow, rootT_succ_pow']
  have hcs : ∀ n, c (n + 1) ^ l = c n := by
    intro n
    apply hinj
    show ((c (n + 1) ^ l : Om l) : ℂ_[l]) = (c n : ℂ_[l])
    rw [hcoe, map_pow, ← hcoe, hc, hc, ← SubmonoidClass.coe_pow, rootT_succ_pow']
  obtain ⟨g, hg⟩ := GlobalTheory.galois_transitive_on_root_systems_of_prime l K _ hπ y (fun n => c n * y n) hy0
    (by rw [hc0, one_mul, hy0]) hys (fun n => by rw [mul_pow, hcs, hys])
  refine ⟨g, hfix _ _ fun n => ?_⟩
  apply Subtype.ext
  refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (GlobalTheory.MemLoc.rootT bk.flat n)).trans ?_
  rw [hy n, GlobalTheory.RingBasics.σC_coe, hg n, rootT_mul']
  rw [MulMemClass.coe_mul, hcoe, map_mul, ← hcoe, ← hcoe, hc n, hy n]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentFrobSolutionsCrisProof
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per
theorem GlobalTheory.PMon.exI_of_ser_core (hser : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧ (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧ ∀ (h : ℕ) (r : ℝ) (y : ℕ → Formalism.Per.Fl l), 2 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧ ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j y) (hcore : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → μ ≠ 0 → ∃ y : Fin h → ℕ → Formalism.Per.Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧ ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0) : ExI := by
  intro l _ P AI T h hh μ hμ hne
  obtain ⟨S, θ, hS, hker, hq, hb⟩ := hser l P AI T
  let μ' : Fin h → ℂ_[l] := fun i => θ ⟨μ i, (hS _).2 (hμ i)⟩
  have hμ' : μ' ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro h0
    exact hi ((hker ⟨μ i, (hS _).2 (hμ i)⟩).1 (congrFun h0 i))
  obtain ⟨y, hy, hz, hind⟩ := hcore l h μ' hh hμ'
  choose b hplus hφ hev using fun a => hb h _ (y a) hh GlobalTheory.RingBasics.norm_p_lt (hy a)
  choose hm hev using hev
  choose hq0 hq using hq
  refine ⟨b, hplus, hφ, ?_, fun a => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have : c = 0 := by
      refine hind c fun j _ => ?_
      have e : ∀ x : P.R.B, ev P j x = P.ιB ((P.φB ^ j) x) := fun x => by
        simp only [ev, AlgHom.coe_pow]
      have h1 : (∑ a, (⟨_, hq0 (c a)⟩ : S) * ⟨_, hm a j⟩) = 0 := by
        apply Subtype.ext
        have := congrArg (fun x => P.ιB ((P.φB ^ j) x)) hc
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, map_zero] at this
        simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, e, ZeroMemClass.coe_zero]
        simpa only [Algebra.smul_def] using this
      have h2 := congrArg θ h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h2
      simpa only [map_mul, hq, hev] using h2
    exact fun i => congrFun this i
  · have h2 : θ (∑ i : Fin h, (⟨μ i, (hS _).2 (hμ i)⟩ : S) * ⟨_, hm a i⟩) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simpa only [map_mul, hev] using hz a
    have := (hker _).1 h2
    simpa only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul] using this

theorem GlobalTheory.PMon.exI_main : ExI := GlobalTheory.PMon.exI_of_ser_core _root_.GlobalTheory.PSer.series_residues GlobalTheory.T.exists_tilt_zeros_untiltFrobeniusDoubleSeries
end

