module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockInvariantsIffIsometry
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitive
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0137
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.InertPlacesGoodSet
public import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0891

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchOfWeilRepresentation
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourierMatchAt_of_weil (hW : WeilEt) (hR : RankOne) (hG : GammaOne) {r : ℕ} {F E : Type}
    [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ)
    (hf' : IsTest f') (hf : IsTest f) (hm : Match M f' f) (a : Inv r F) (ha : Delta a ≠ 0)
    (hsep : (companion a.1).charpoly.Separable) :
    MatchAt M (fourG M ψ f') (fourU M ψ f) a := by
  obtain ⟨A, τ, hτ⟩ := _root_.GlobalTheory.JR.exists_et_isGen_companion F E r a.1 hsep
  obtain ⟨hbij, hmom⟩ := _root_.GlobalTheory.JR.EtInv.invK_regular_iff_isUnit F E A r τ a.1 a.2.2 hτ
  obtain ⟨a₀, ha₀⟩ := hbij.2 a.2.1
  have ha₀' : (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * a₀)) = a.2.1 := ha₀
  have hinv : A.invK τ a.1 a.2.2 a₀ = a := by
    simp only [Et.invK, ha₀']
  have hu₀ : IsUnit a₀ := (hmom a₀).2.mp (by rw [hinv]; exact ha)
  obtain ⟨⟨m⟩, -⟩ := _root_.GlobalTheory.JR.exists_meas_and_scale F E A ψ hψ
  obtain ⟨-, -, -, -, -, -, ⟨S, -, hS⟩, -⟩ := _root_.GlobalTheory.JR.EtFacts.main F E A
  obtain ⟨φ', κ, hφ', hlin⟩ := _root_.GlobalTheory.JR.LinDesc.descent F E A ψ hψ m r M τ a.1 a.2.2 hτ f' hf'
  obtain ⟨-, -, huniq, -⟩ := _root_.GlobalTheory.JR.HermInv.herm_invariants F E r
  obtain ⟨-, horbU, -, -⟩ := _root_.GlobalTheory.JR.OrbLC.orbital_integrals_invariant_locally_constant F E r M
  obtain ⟨hL11a, hL11b⟩ := _root_.GlobalTheory.EtIsom.herm_iff_isom F E A r τ a.1 a.2.2 hτ
  have key : ∀ x : A.Kˣ, ∃ φx : A.L → ℂ, IsTest φx ∧
      ((∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j) →
        ∃ (j : A.L ≃ₗ[E] (Fin r → E)) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), A.IsIsom (x : A.K) j ∧
          (∀ y, HasInv ((Ax, j y, a.2.2) : Hn r F E) (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) ∧
          ∀ y : A.L, IsUnit y → orbU M f (Ax, j y, a.2.2) = A.orbL m.ν φx y ∧
            orbU M (fourU M ψ f) (Ax, j y, a.2.2) = A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) φx) y) ∧
      ((¬ ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j) → φx = 0) := by
    intro x
    by_cases hx : ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j
    · obtain ⟨j, hj⟩ := hx
      obtain ⟨Ax, hAx, hinvAx⟩ := hL11b (x : A.K) j hj
      obtain ⟨φx, hφx, hrel⟩ := _root_.GlobalTheory.JR.unitary_orbital_descent F E A ψ hψ m r M τ a.1 a.2.2 hτ x j hj Ax hAx f hf
      exact ⟨φx, hφx, fun _ => ⟨j, Ax, hj, hinvAx, hrel⟩, fun h => absurd ⟨j, hj⟩ h⟩
    · exact ⟨0, ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩, fun h => absurd h hx, fun _ => rfl⟩
  choose φ hφt hφi hφ0 using key
  choose γ Wr hWr using fun x : A.Kˣ => hW F E A ψ hψ x (m.μL x) (m.sdL x)
  have hunit : ∀ (x : A.Kˣ) (y : A.L), IsUnit y → IsUnit ((x : A.K) * A.NL y) := fun x y hy =>
    x.isUnit.mul (hy.map (Algebra.norm A.K))
  have hyp : ∀ x ∈ S, ∀ y : A.L, IsUnit y → κ * A.orbK m.μK φ' (x * A.NL y) = A.orbL m.ν (φ x) y := by
    intro x _ y hy
    have hb := hunit x y hy
    rw [← (hlin _ hb).1]
    by_cases hx : ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j
    · obtain ⟨j, Ax, -, hinvAx, hrel⟩ := hφi x hx
      rw [← (hrel y hy).1]
      exact (hm _ ((hmom _).2.mpr hb)).1 _ (hinvAx y)
    · rw [hφ0 x hx]
      have h0 : orbG M f' (sec (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) = 0 := by
        apply (hm _ ((hmom _).2.mpr hb)).2
        rintro ⟨X, hX⟩
        obtain ⟨j, hj, -⟩ := hL11a _ X hb hX (x : A.K) y hy rfl
        exact hx ⟨j, hj⟩
      rw [h0]
      simp [Et.orbL]
  have hRk := hR F E A ψ hψ m S hS γ Wr (fun x _ => hWr x) φ' φ κ hφ' (fun x _ => hφt x) hyp
  have hG1 : ∀ (x : A.Kˣ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom (x : A.K) j → γ x = 1 :=
    fun x j hj => hG F E A ψ hψ x (m.μL x) (m.sdL x) A.etaK (γ x) (Wr x) (hWr x) r j hj
  obtain ⟨x, ⟨hxS, y, hy, hxy⟩, -⟩ := hS hu₀.unit
  have hxy' : a₀ = x * A.NL y := by simpa using hxy
  have hb := hunit x y hy
  have hlhs : orbG M (fourG M ψ f') (sec a) =
      γ x * A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) (φ x)) y := by
    calc orbG M (fourG M ψ f') (sec a)
        = orbG M (fourG M ψ f') (sec (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) := by rw [← hxy', hinv]
      _ = κ * A.orbK m.μK (A.fourK m.μK ψ φ') ((x : A.K) * A.NL y) := (hlin _ hb).2
      _ = _ := hRk x hxS y hy
  constructor
  · intro X hX
    have hX' : HasInv X (A.invK τ a.1 a.2.2 a₀) := by rw [hinv]; exact hX
    obtain ⟨j₁, hj₁, -⟩ := hL11a a₀ X hu₀ hX' (x : A.K) y hy hxy'
    obtain ⟨j, Ax, hj, hinvAx, hrel⟩ := hφi x ⟨j₁, hj₁⟩
    have hXa : HasInv ((Ax, j y, a.2.2) : Hn r F E) a := by
      have := hinvAx y
      rw [← hxy', hinv] at this
      exact this
    obtain ⟨g, hg, -⟩ := huniq _ X a ha hXa hX
    rw [hlhs, hG1 x j hj, one_mul, ← (hrel y hy).2, ← hg, horbU]
  · intro hno
    have hx : ¬ ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j := by
      intro hx
      obtain ⟨j, Ax, -, hinvAx, -⟩ := hφi x hx
      have := hinvAx y
      rw [← hxy', hinv] at this
      exact hno ⟨_, this⟩
    rw [hlhs, hφ0 x hx]
    simp [fourB, Et.orbL]

theorem fourierMatch_of_weil : WeilEt → RankOne → GammaOne → ∀ r, FourierMatch r := by
  intro hW hR hG r F E _ _ _ _ _ M ψ hψ f' f hf' hf hm
  obtain ⟨h4G, h4U, -⟩ := _root_.GlobalTheory.fourier_test_unit F E r M ψ hψ
  exact (_root_.GlobalTheory.JR.DenseMatch.match_of_dense F E r M _ _ (h4G f' hf') (h4U f hf)).1
    (fun a ha hsep => fourierMatchAt_of_weil hW hR hG M ψ hψ f' f hf' hf hm a ha hsep)

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSucc
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.UnitStep

section Basic
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def qU {r : ℕ} (X : Hn r F E) : F := Algebra.trace F E (star X.2.1 ⬝ᵥ X.2.1) / 2

theorem mom_act_zero {r : ℕ} (g : GL (Fin r) F) (Y : Gl r F) : mom (act g Y) 0 = mom Y 0 := by
  simp only [mom, act, pow_zero, one_mulVec]
  rw [dotProduct_mulVec, vecMul_vecMul]
  have : ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (g : Matrix (Fin r) (Fin r) F) = 1 := by
    simp
  rw [this, vecMul_one]

theorem qU_actU {r : ℕ} (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : qU (actU g X) = qU X := by
  simp only [qU, actU]
  congr 2
  rw [Matrix.star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  have : (g.1)ᴴ * g.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff').1 g.2
  rw [this, vecMul_one]

theorem mom_sec_zero {r : ℕ} (a : Inv (r + 1) F) : mom (sec a) 0 = a.2.1 0 := by
  simp [mom, sec, dotProduct]

theorem qU_of_hasInv [Unram F E] {r : ℕ} {X : Hn (r + 1) F E} {a : Inv (r + 1) F} (h : HasInv X a) :
    qU X = mom (sec a) 0 := by
  have h1 := congrArg (fun p => p.2.1 0) h
  simp only [inv, Inv.map, Hn.toGl, mom] at h1
  rw [show ((0 : Fin (r + 1)) : ℕ) = 0 from rfl, pow_zero, one_mulVec] at h1
  rw [mom_sec_zero, qU, h1, Algebra.trace_algebraMap, Unram.finrank_eq]
  haveI := (Unram.charZero (F := F) (E := E))
  rw [nsmul_eq_mul]; push_cast; field_simp

theorem orbG_mul {r : ℕ} (M : Meas r F E) (φ : F → ℂ) (f' : Gl r F → ℂ) (Y : Gl r F) :
    orbG M (fun Y => φ (mom Y 0) * f' Y) Y = φ (mom Y 0) * orbG M f' Y := by
  simp only [orbG, mom_act_zero, mul_assoc]
  exact integral_const_mul _ _

theorem orbU_mul {r : ℕ} (M : Meas r F E) (φ : F → ℂ) (f : Hn r F E → ℂ) (X : Hn r F E) :
    orbU M (fun X => φ (qU X) * f X) X = φ (qU X) * orbU M f X := by
  simp only [orbU, qU_actU]
  exact integral_const_mul _ _

theorem matchAt_mul [Unram F E] {r : ℕ} (M : Meas (r + 1) F E) (φ : F → ℂ) {f' : Gl (r + 1) F → ℂ}
    {f : Hn (r + 1) F E → ℂ} {a : Inv (r + 1) F} (h : MatchAt M f' f a) :
    MatchAt M (fun Y => φ (mom Y 0) * f' Y) (fun X => φ (qU X) * f X) a :=
  ⟨fun X hX => by rw [orbG_mul, orbU_mul, h.1 X hX, qU_of_hasInv hX],
    fun hn => by rw [orbG_mul, h.2 hn, mul_zero]⟩

theorem matchAt_mul_zero [Unram F E] {r : ℕ} (M : Meas (r + 1) F E) (φ : F → ℂ) (f' : Gl (r + 1) F → ℂ)
    (f : Hn (r + 1) F E → ℂ) {a : Inv (r + 1) F} (h0 : φ (mom (sec a) 0) = 0) :
    MatchAt M (fun Y => φ (mom Y 0) * f' Y) (fun X => φ (qU X) * f X) a :=
  ⟨fun X hX => by rw [orbG_mul, orbU_mul, qU_of_hasInv hX, h0, zero_mul, zero_mul],
    fun _ => by rw [orbG_mul, h0, zero_mul]⟩

theorem matchAt_of_mul [Unram F E] {r : ℕ} (M : Meas (r + 1) F E) (φ : F → ℂ) {f' : Gl (r + 1) F → ℂ}
    {f : Hn (r + 1) F E → ℂ} {a : Inv (r + 1) F} (h0 : φ (mom (sec a) 0) ≠ 0)
    (h : MatchAt M (fun Y => φ (mom Y 0) * f' Y) (fun X => φ (qU X) * f X) a) : MatchAt M f' f a := by
  refine ⟨fun X hX => ?_, fun hn => ?_⟩
  · have := h.1 X hX
    rw [orbG_mul, orbU_mul, qU_of_hasInv hX] at this
    exact mul_left_cancel₀ h0 this
  · have := h.2 hn
    rw [orbG_mul] at this
    exact (mul_eq_zero.1 this).resolve_left h0

theorem match_zero {r : ℕ} (M : Meas r F E) : Match M (0 : Gl r F → ℂ) (0 : Hn r F E → ℂ) := by
  intro a _
  refine ⟨fun X _ => ?_, fun _ => ?_⟩ <;> simp [orbG, orbU]

theorem isTest_sub {X : Type} [TopologicalSpace X] {f g : X → ℂ} (hf : IsTest f) (hg : IsTest g) :
    IsTest (f - g) :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem wS_inv : (wS F)⁻¹ = wS F * wS F * wS F := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  simp [wS, Matrix.mul_fin_two, Matrix.one_fin_two]

theorem nS_inv (t : F) : (nS t)⁻¹ = nS (-t) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F) * !![1, -t; 0, 1] = 1
  simp [Matrix.mul_fin_two, Matrix.one_fin_two]


variable (E) in
theorem submonoid_eq_top [Unram F E] (S : Submonoid (SpecialLinearGroup (Fin 2) F)) (hw : wS F ∈ S)
    (hn : ∀ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) → nS t ∈ S) (x : SpecialLinearGroup (Fin 2) F) : x ∈ S := by
  have hgen := _root_.GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top F E
  have hx : x ∈ Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) := by
    rw [hgen]; trivial
  rw [← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid] at hx
  refine (Submonoid.closure_le (S := S)).2 ?_ hx
  rintro g ((hg | ⟨t, ht, rfl⟩) | hg)
  · rw [Set.mem_singleton_iff.1 hg]; exact hw
  · exact hn t ht
  · rcases hg with hg | ⟨t, ht, hg⟩
    · rw [Set.mem_singleton_iff] at hg
      rw [← inv_inv g, hg, wS_inv]; exact S.mul_mem (S.mul_mem hw hw) hw
    · rw [← inv_inv g, hg, nS_inv]
      exact hn (-t) (fun y hy => by rw [neg_mul, norm_neg]; exact ht y hy)

end Basic
end GlobalTheory.JR.UnitStep

namespace GlobalTheory.JR.UnitStep

theorem unitMatch_succ : WeilEt → GammaOne → ∀ r : ℕ, FourierMatch (r + 1) → UnitMatch r → UnitMatch (r + 1) := by
  intro hWe hGo r hF hU F E _ _ _ _ _ M
  obtain ⟨ψ, hψ⟩ := (_root_.GlobalTheory.StdChar.psi_conductor F E).1
  obtain ⟨W1, hW1r, hW1⟩ := _root_.GlobalTheory.JR.weil_repG F E (r + 1) M ψ hψ
  obtain ⟨W2, hW2r, hW2⟩ := _root_.GlobalTheory.weilSL2_hermitian hWe hGo F E (r + 1) M ψ hψ
  obtain ⟨hTG, hTU, htG, htU, hfG, hfU⟩ := _root_.GlobalTheory.fourier_test_unit F E (r + 1) M ψ hψ

  have hN1 : ∀ f, IsTest f → ∀ t : F, W1 (nS t) f = fun Y => (fun z => ψ (t * z)) (mom Y 0) * f Y :=
    fun f hf t => funext fun Y => (hW1 f hf).1 t Y
  have hN2 : ∀ f, IsTest f → ∀ t : F, W2 (nS t) f = fun X => (fun z => ψ (t * z)) (qU X) * f X :=
    fun f hf t => funext fun X => by
      rw [(hW2 f hf).1 t X, qU, mul_div_assoc]

  let S : Submonoid (SpecialLinearGroup (Fin 2) F) :=
    { carrier := {g | ∀ f' f, IsTest f' → IsTest f → Match M f' f → Match M (W1 g f') (W2 g f)}
      one_mem' := fun f' f hf' hf hm => by rw [hW1r.2.1 f' hf', hW2r.2.1 f hf]; exact hm
      mul_mem' := fun {g h} hg hh f' f hf' hf hm => by
        rw [hW1r.2.2.1 g h f' hf', hW2r.2.2.1 g h f hf]
        exact hg _ _ (hW1r.1 h f' hf') (hW2r.1 h f hf) (hh f' f hf' hf hm) }
  have hS : ∀ g, g ∈ S := submonoid_eq_top E S
    (fun f' f hf' hf hm => by rw [(hW1 f' hf').2, (hW2 f hf).2]; exact hF F E M ψ hψ f' f hf' hf hm)
    (fun t _ f' f hf' hf hm => by
      rw [hN1 f' hf' t, hN2 f hf t]
      exact fun a ha => matchAt_mul M (fun z => ψ (t * z)) (hm a ha))

  let u' := unitG (r + 1) F
  let u := unitU (r + 1) F E
  let S' : Submonoid (SpecialLinearGroup (Fin 2) F) :=
    { carrier := {g | Match M (W1 g u' - u') (W2 g u - u)}
      one_mem' := by
        show Match M (W1 1 u' - u') (W2 1 u - u)
        rw [hW1r.2.1 u' htG, hW2r.2.1 u htU, sub_self, sub_self]; exact match_zero M
      mul_mem' := fun {g h} hg hh => by
        show Match M (W1 (g * h) u' - u') (W2 (g * h) u - u)
        have e1 : W1 (g * h) u' - u' = W1 g (W1 h u' - u') + (W1 g u' - u') := by
          have hs : W1 h u' - u' = (-1 : ℂ) • u' + W1 h u' := by
            funext Y; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
          rw [hW1r.2.2.1 g h u' htG, hs, hW1r.2.2.2 g (-1) u' (W1 h u') htG (hW1r.1 h u' htG)]
          funext Y; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        have e2 : W2 (g * h) u - u = W2 g (W2 h u - u) + (W2 g u - u) := by
          have hs : W2 h u - u = (-1 : ℂ) • u + W2 h u := by
            funext X; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
          rw [hW2r.2.2.1 g h u htU, hs, hW2r.2.2.2 g (-1) u (W2 h u) htU (hW2r.1 h u htU)]
          funext X; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        have d1 : IsTest (W1 h u' - u') := isTest_sub (hW1r.1 h u' htG) htG
        have d2 : IsTest (W2 h u - u) := isTest_sub (hW2r.1 h u htU) htU
        rw [e1, e2]
        exact _root_.GlobalTheory.JR.match_add F E (r + 1) M _ _ _ _ (hW1r.1 g _ d1) (isTest_sub (hW1r.1 g u' htG) htG)
          (hW2r.1 g _ d2) (isTest_sub (hW2r.1 g u htU) htU) (hS g _ _ d1 d2 hh) hg }
  have hD1 : ∀ t : F, W1 (nS t) u' - u' = fun Y => (fun z => ψ (t * z) - 1) (mom Y 0) * u' Y := by
    intro t; rw [hN1 u' htG t]; funext Y; simp only [Pi.sub_apply]; ring
  have hD2 : ∀ t : F, W2 (nS t) u - u = fun X => (fun z => ψ (t * z) - 1) (qU X) * u X := by
    intro t; rw [hN2 u htU t]; funext X; simp only [Pi.sub_apply]; ring
  have hS' : ∀ g, g ∈ S' := submonoid_eq_top E S'
    (by
      show Match M (W1 (wS F) u' - u') (W2 (wS F) u - u)
      rw [(hW1 u' htG).2, (hW2 u htU).2, hfG, hfU, sub_self, sub_self]; exact match_zero M)
    (fun t ht => by
      show Match M (W1 (nS t) u' - u') (W2 (nS t) u - u)
      rw [hD1 t, hD2 t]
      intro a ha
      by_cases h1 : 1 ≤ ‖mom (sec a) 0‖
      · exact matchAt_mul M (fun z => ψ (t * z) - 1) (_root_.GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm r hU F E M a ha h1)
      · refine matchAt_mul_zero M (fun z => ψ (t * z) - 1) u' u ?_
        have : ‖t * mom (sec a) 0‖ ≤ 1 := ht _ (lt_of_not_ge h1)
        simp [hψ.1 _ this])

  refine (_root_.GlobalTheory.JR.DenseMatch.match_of_dense F E (r + 1) M u' u htG htU).2 (Nat.succ_pos r) ?_
  intro a ha ha0
  obtain ⟨x, hx, -⟩ := hψ.2
  have hm := hS' (nS (x / mom (sec a) 0))
  change Match M (W1 (nS _) u' - u') (W2 (nS _) u - u) at hm
  rw [hD1, hD2] at hm
  refine matchAt_of_mul M (fun z => ψ (x / mom (sec a) 0 * z) - 1) ?_ (hm a ha)
  simp only [div_mul_cancel₀ x ha0]
  exact sub_ne_zero.2 hx

end GlobalTheory.JR.UnitStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LongOrbitsRowColengthInertLocalisation
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.RowBLong

theorem logb_le_self {l : ℕ} (hl : 11 ≤ l) {y : ℝ} (hy : 0 < y) : Real.logb l y ≤ y := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hlog : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have h1 := Real.log_le_sub_one_of_pos hy
  unfold Real.logb
  rcases le_or_gt 0 (Real.log y) with h | h
  · calc Real.log y / Real.log l ≤ Real.log y := div_le_self h hlog
      _ ≤ y := by linarith
  · have : Real.log y / Real.log l < 0 := div_neg_of_neg_of_pos h (by linarith)
    linarith

theorem logb_le_split {l : ℕ} (hl : 11 ≤ l) (j : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    Real.logb l H ≤ H / ((l : ℝ) - 1) ^ (j + 1) + ((j : ℝ) + 1) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hm : 0 < ((l : ℝ) - 1) ^ (j + 1) := pow_pos (by linarith) _
  have hl1 : (1 : ℝ) < l := by linarith
  rcases hH.eq_or_lt with h0 | hpos
  · rw [← h0]; simp; positivity
  have hsplit : Real.logb l H = Real.logb l (H / ((l : ℝ) - 1) ^ (j + 1)) + Real.logb l (((l : ℝ) - 1) ^ (j + 1)) := by
    rw [Real.logb_div hpos.ne' hm.ne']; ring
  have h2 : Real.logb l (((l : ℝ) - 1) ^ (j + 1)) ≤ (j : ℝ) + 1 := by
    rw [Real.logb_pow]
    have h3 : Real.logb l ((l : ℝ) - 1) ≤ 1 := by
      have := Real.logb_le_logb_of_le hl1 (by linarith : (0:ℝ) < l - 1) (by linarith : (l:ℝ) - 1 ≤ l)
      rwa [Real.logb_self_eq_one hl1] at this
    push_cast
    have : (0:ℝ) ≤ (j:ℝ) + 1 := by positivity
    nlinarith
  rw [hsplit]
  have := logb_le_self hl (div_pos hpos hm)
  linarith

theorem bracket_le {l : ℕ} (hl : 11 ≤ l) (j : ℕ) {H G0 hB GP large₂ : ℝ} (hH0 : 0 ≤ H) (hG0 : 0 ≤ G0)
    (hGP : G0 ≤ GP) (hB0 : 0 ≤ hB) (hLg : 0 ≤ large₂) (hH : H ≤ hB ∨ H ≤ G0) :
    H / ((l : ℝ) - 1) ^ (j + 1) + (G0 + 1) * ((j : ℝ) + 1) + Real.logb l H ≤
      3 * (hB / ((l : ℝ) - 1) ^ (j + 1) + (GP + 1) * ((j : ℝ) + 1) + large₂) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hm1 : 1 ≤ ((l : ℝ) - 1) ^ (j + 1) := one_le_pow₀ (by linarith)
  have hm : 0 < ((l : ℝ) - 1) ^ (j + 1) := by linarith
  have hlog := logb_le_split hl j hH0
  have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hBm : 0 ≤ hB / ((l : ℝ) - 1) ^ (j + 1) := div_nonneg hB0 hm.le
  have hGj : (G0 + 1) * ((j : ℝ) + 1) ≤ (GP + 1) * ((j : ℝ) + 1) := by nlinarith
  have hj1 : (j : ℝ) + 1 ≤ (GP + 1) * ((j : ℝ) + 1) := by nlinarith
  rcases hH with h | h
  · have : H / ((l : ℝ) - 1) ^ (j + 1) ≤ hB / ((l : ℝ) - 1) ^ (j + 1) := div_le_div_of_nonneg_right h hm.le
    nlinarith
  · have h1 : H / ((l : ℝ) - 1) ^ (j + 1) ≤ H := div_le_self hH0 hm1
    have h2 : 2 * G0 + (j : ℝ) + 1 ≤ 2 * (G0 + 1) * ((j : ℝ) + 1) := by nlinarith
    nlinarith

end GlobalTheory.RowBLong

namespace GlobalTheory.RowBLong

open Formalism.MainNotions.N in
theorem nLet_eq_nLam {D : D7} {L : SizeData₂ D} {HW : HWOf D.loc} {i : D.nd.Loc}
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL} {Wd : WordDat (nLet i w hw)}
    (hb : WordBase L HW i r ρ π w hw Cx hG Wd) : nLet i w hw = Formalism.MainNotions.TwistedPlaces.nLam D w := by
  have hK : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hb.unram
  have h1 : nLet i w hw = Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 :=
    (IntermediateField.equivOfEq hK).toLinearEquiv.finrank_eq
  rw [h1]
  exact hb.deg

end GlobalTheory.RowBLong

namespace GlobalTheory.RowBLong

attribute [local instance] Formalism.MainNotions.N.nLet_neZero

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), WachCoordinates.Conclusion2 D C₂ → 1 ≤ C₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → LocalRepresentationBoundCondition L HW C₂ i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowB L C₂ (D.nd.l i)) := by
  intro D L P HW C₂ i r ρ π dc hA hC _ h11 hJ
  intro w hw _ C hCg
  obtain ⟨hur, hWd⟩ := hJ w hw
  have hg : Good (D.nbr i w hw).Kw 1 C.LL := hCg.good_one (by omega) (le_trans (le_inf le_rfl hur) le_sup_left)
  obtain ⟨Wd, hb, hB⟩ := hWd C hg
  have hrow := GlobalTheory.Survey.InertPlacesGoodSet.rowL_of_wordsB hA h11 hb hB
  refine GlobalTheory.T.rowBound_at_place_of_latticeColengthBound D i r ρ π w hw C _ _ hrow ?_
  have hn : ((nLet i w hw : ℕ) : ℝ) = (Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) := by
    exact_mod_cast nLet_eq_nLam hb
  have hl' : (11 : ℝ) ≤ D.nd.l i := by exact_mod_cast h11
  have hbr := bracket_le h11 (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i))
    (H := (WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) (G0 := ((Wd.w + Wd.S + Wd.η : ℕ) : ℝ))
    (hB := Formalism.MainNotions.TwistedPlaces.hB L) (GP := Formalism.MainNotions.TwistedPlaces.GP L) (large₂ := Formalism.MainNotions.TwistedPlaces.large₂ L)
    (by positivity) (by positivity)
    (by
      unfold Formalism.MainNotions.TwistedPlaces.GP
      have := hb.w_le; have := hb.S_le; have := hb.η_le
      push_cast; linarith)
    (by linarith [Formalism.MainNotions.TwistedPlaces.one_le_hB L]) (Formalism.MainNotions.TwistedPlaces.Lg_nonneg L)
    (by
      unfold WachCoordinates.hCor
      split_ifs
      · left; have := hb.h_le; push_cast; linarith
      · right; exact le_rfl)
  have key : C₂ * (((nLet i w hw : ℕ) : ℝ) + 1) * D.R.r *
      ((WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) / ((D.nd.l i : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) + 1) +
        (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) +
        Real.logb (D.nd.l i) (WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) ≤
      3 * C₂ * coreB L (D.nd.l i) w := by
    unfold coreB
    rw [hn]
    have h0 : 0 ≤ C₂ * ((Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) + 1) * D.R.r := by
      have : (0:ℝ) ≤ C₂ := by linarith
      positivity
    calc _ ≤ C₂ * ((Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) + 1) * D.R.r *
          (3 * (Formalism.MainNotions.TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) + 1) +
            (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L)) :=
          mul_le_mul_of_nonneg_left hbr h0
      _ = _ := by ring
  unfold lenRowB ratIn
  split_ifs with hlt
  · have := (exists_rat_btwn hlt).choose_spec
    linarith [this.1]
  · push_neg at hlt
    have hc0 : coreB L (D.nd.l i) w ≤ 0 := by linarith
    have : 3 * C₂ * coreB L (D.nd.l i) w ≤ 0 := by
      have : (0:ℝ) ≤ 3 * C₂ := by linarith
      nlinarith
    simp only [Rat.cast_zero]
    linarith

end GlobalTheory.RowBLong
end
end

