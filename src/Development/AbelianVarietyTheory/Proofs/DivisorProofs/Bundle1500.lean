module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionCompactLevelContinuous
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

open Pointwise

namespace GlobalTheory.ResLine.HtCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField E] in
theorem inv_eigen {x : Matrix (Fin n) (Fin 1) E} {p : GAd σ J} {l : (AF F ⊗[F] E)ˣ}
    (hp : (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) :
    (matHom _ σ J p⁻¹).1 * adMat F x = (l⁻¹).1 • adMat F x := by
  have h1 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : l.1 • ((matHom _ σ J p⁻¹).1 * adMat F x) = adMat F x := by
    rw [← Matrix.mul_smul, ← hp, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  calc _ = ((l⁻¹).1 * l.1) • ((matHom _ σ J p⁻¹).1 * adMat F x) := by rw [Units.inv_mul, one_smul]
    _ = _ := by rw [← smul_smul, h2]

omit [NumberField F] in
theorem exists_col_ne {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    ∃ i, col X i 0 ≠ 0 := by
  by_contra hc
  push Not at hc
  have h0 : ∀ j, X j 0 = 0 := fun j => hc j
  have := congrFun (congrFun hW.xy 0) 0
  simp [Matrix.mul_apply, Formalism.UG.cT, h0] at this

set_option linter.style.haveILetI false in
theorem isCompact_and_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h →
    IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ Continuous h := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS
  obtain ⟨hCM, -, -, hW, hA, hI1, hI2⟩ := hS
  let _ : Submodule.IsFullLattice E L := hA.lat
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll hCM J L a
  refine ⟨hK, ?_⟩
  obtain ⟨i, hi⟩ := exists_col_ne hW
  set x := col X with hx
  have hm : Continuous fun g : GAd σ J => (matHom _ σ J g).1 :=
    Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous
  let Λ : GAd σ J → AF F ⊗[F] E := fun g =>
    ((matHom _ σ J g).1 * adMat F x) i 0 * inclR (F := F) (AF F) (x i 0)⁻¹
  have hΛ : Continuous Λ := ((hm.matrix_mul continuous_const).matrix_elem i 0).mul continuous_const
  have key : ∀ p (l : (AF F ⊗[F] E)ˣ), (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → l.1 = Λ p := by
    intro p l hl
    have e := congrFun (congrFun hl i) 0
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at e
    simp only [Λ, e, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one]
  let P : Set (GAd σ J) := {p | (matHom _ σ J p).1 * adMat F x = Λ p • adMat F x ∧ Λ p * Λ p⁻¹ = 1}
  have memP : ∀ p, (∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) → p ∈ P := by
    rintro p ⟨l, hl⟩
    have e1 := key p l hl
    have e2 := key p⁻¹ l⁻¹ (inv_eigen hl)
    exact ⟨by rw [← e1]; exact hl, by rw [← e1, ← e2, Units.mul_inv]⟩
  have hPc : IsClosed P :=
    (isClosed_eq (hm.matrix_mul continuous_const) (hΛ.smul continuous_const)).inter
      (isClosed_eq (hΛ.mul (hΛ.comp continuous_inv)) continuous_const)
  let u : P → (AF F ⊗[F] E)ˣ := fun p => ⟨Λ p, Λ p.1⁻¹, p.2.2, by rw [mul_comm]; exact p.2.2⟩
  have hu : Continuous u := Units.continuous_iff.2
    ⟨hΛ.comp continuous_subtype_val, (hΛ.comp continuous_inv).comp continuous_subtype_val⟩
  let f : P → ℝ := fun p => (absE F E (u p) : ℝ)
  have hf : Continuous f := NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp hu)
  have hval : ∀ p : P, ∀ k ∈ levelAll σ J L a, h (p.1 * k) = f p := fun p k hk =>
    hI2 p.1 (u p) p.2.1 k hk
  rw [continuous_iff_isClosed]
  intro s hs
  have hpre : h ⁻¹' s = (Subtype.val '' (f ⁻¹' s)) * (levelAll σ J L a : Set (GAd σ J)) := by
    ext g; constructor
    · intro hg
      obtain ⟨p, l, hl, k, hk, rfl⟩ := hI1 g
      have hp : p ∈ P := memP p ⟨l, hl⟩
      refine ⟨p, ⟨⟨p, hp⟩, ?_, rfl⟩, k, hk, rfl⟩
      show f ⟨p, hp⟩ ∈ s
      rw [← hval ⟨p, hp⟩ k hk]; exact hg
    · rintro ⟨_, ⟨p, hp, rfl⟩, k, hk, rfl⟩
      show h (p.1 * k) ∈ s
      rw [hval p k hk]; exact hp
  rw [hpre]
  exact (hPc.isClosedEmbedding_subtypeVal.isClosedMap _ (hs.preimage hf)).mul_right_of_isCompact hK

end GlobalTheory.ResLine.HtCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeEqRowSpaceOfSandwichDatum
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.RowSpace

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]


variable (p O) in
def ghostHom (n : ℕ) : Ainf p O →+* O where
  toFun := ghost p O n
  map_one' := by
    show WittVector.fontaineTheta O p (_ ^[n] 1) = 1
    rw [iterate_map_one, map_one]
  map_mul' := ghost_mul n
  map_zero' := ghost_zero n
  map_add' := ghost_add n

theorem ghostHom_apply (n : ℕ) (a : Ainf p O) : ghostHom p O n a = ghost p O n a := rfl

def dotLin {R : Type} [CommRing R] {h : ℕ} (v : Fin h → R) : (Fin h → R) →ₗ[R] R where
  toFun w := v ⬝ᵥ w
  map_add' := dotProduct_add v
  map_smul' c w := by simp [dotProduct_smul]

theorem dotLin_apply {R : Type} [CommRing R] {h : ℕ} (v w : Fin h → R) : dotLin v w = v ⬝ᵥ w := rfl

def toA {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (t : G.Tate) :
    Fin h → Ainf p O := fun i => ofPadic p O (e t i)

theorem toA_add {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (t t' : G.Tate) : toA e (t + t') = toA e t + toA e t' := by
  ext i; simp [toA]

theorem toA_smul {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (c : ℤ_[p]) (t : G.Tate) : toA e (c • t) = ofPadic p O c • toA e t := by
  ext i; simp [toA]

theorem toA_single {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (i : Fin h) : toA e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
  ext j; by_cases hij : j = i <;> simp [toA, Pi.single_apply, hij]

theorem toO_single {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (i : Fin h) : toO e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
  ext j; by_cases hij : j = i <;> simp [toO, Pi.single_apply, hij]

def rowMap {G : PDivGroup p O} {h : ℕ} (F : Matrix (Fin h) (Fin h) (Ainf p O))
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) : (Fin h → Ainf p O) →ₗ[Ainf p O] TDual G where
  toFun r :=
    { toFun := fun t => r ⬝ᵥ (F *ᵥ toA e t)
      map_add' := fun t t' => by rw [toA_add, mulVec_add, dotProduct_add]
      map_smul' := fun c t => by
        rw [toA_smul, mulVec_smul, dotProduct_smul] }
  map_add' r r' := LinearMap.ext fun t => add_dotProduct r r' _
  map_smul' a r := LinearMap.ext fun t => smul_dotProduct a r _

theorem rowMap_apply {G : PDivGroup p O} {h : ℕ} (F : Matrix (Fin h) (Fin h) (Ainf p O))
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (r : Fin h → Ainf p O) (t : G.Tate) :
    rowMap F e r t = r ⬝ᵥ (F *ᵥ toA e t) := rfl

theorem F_map_ghost {ε : PreTilt O p} {h : ℕ} (D : Datum ε h ℤ_[p])
    (hphi : ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a) (n : ℕ) :
    ∃ X : Matrix (Fin h) (Fin h) O,
      D.F.map (ghostHom p O n) = X * D.F.map (WittVector.fontaineTheta O p) := by
  induction n with
  | zero => exact ⟨1, by rw [Matrix.one_mul]; rfl⟩
  | succ n ih =>
    obtain ⟨X, hX⟩ := ih
    refine ⟨D.Ψ.map (ghostHom p O (n + 1)) * X, ?_⟩
    have e1 : D.F.map (ghostHom p O (n + 1)) =
        D.Ψ.map (ghostHom p O (n + 1)) * D.F.map (ghostHom p O n) := by
      conv_lhs => rw [D.F_eq]
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hphi n _
    rw [e1, hX, Matrix.mul_assoc]

theorem G_map_ghost {ε : PreTilt O p} {h : ℕ} (D : Datum ε h ℤ_[p])
    (hG : D.G = D.G.map (phiInv p O) * D.Ψ')
    (hphi : ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a) (n : ℕ) :
    ∃ Y : Matrix (Fin h) (Fin h) O,
      D.G.map (ghostHom p O n) = D.G.map (WittVector.fontaineTheta O p) * Y := by
  induction n with
  | zero => exact ⟨1, by rw [Matrix.mul_one]; rfl⟩
  | succ n ih =>
    obtain ⟨Y, hY⟩ := ih
    refine ⟨Y * D.Ψ'.map (ghostHom p O (n + 1)), ?_⟩
    have e1 : D.G.map (ghostHom p O (n + 1)) =
        D.G.map (ghostHom p O n) * D.Ψ'.map (ghostHom p O (n + 1)) := by
      conv_lhs => rw [hG]
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hphi n _
    rw [e1, hY, Matrix.mul_assoc]

end SlopeTestRemainingChoices

theorem latt_eq_rowSpace : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (h : ℕ) (D : Datum ε h ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (fil : G.dual.omega ≃ₗ[O] D.Fil), (∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin h → O)) → ∃ L : (Fin h → Ainf p O) ≃ₗ[Ainf p O] latt G, ∀ r t, (L r).1 t = r ⬝ᵥ (D.F *ᵥ fun i => ofPadic p O (e t i)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G h D e fil hal
  obtain ⟨-, hofP, hmu, -, -, hphi⟩ := _root_.GlobalTheory.PDivLat.ghost_values p C v O hv ε hε
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  obtain ⟨hdom, -, -, -, hν, hξ, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε1
  haveI := hdom
  have hμ : Sandwich.mu ε ≠ 0 := by
    rw [← xi_mul_nu]
    exact mul_ne_zero hξ fun h0 => hν (by rw [h0, map_zero])
  have hFG : D.F * D.G = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) :=
    GlobalTheory.SelfDualFil.mul_eq_smul_comm hμ D.G_mul_F
  have hGeq := GlobalTheory.SelfDualFil.G_eq hμ hξ D
  have hθμ : WittVector.fontaineTheta O p (Sandwich.mu ε) = 0 := hmu 0

  have hzero : ∀ X Y : Matrix (Fin h) (Fin h) (Ainf p O), X * Y = Sandwich.mu ε • 1 →
      ∀ w : Fin h → O, X.map (WittVector.fontaineTheta O p) *ᵥ
        (Y.map (WittVector.fontaineTheta O p) *ᵥ w) = 0 := by
    intro X Y hXY w
    rw [mulVec_mulVec, ← Matrix.map_mul, hXY]
    ext i
    simp [Matrix.mulVec, dotProduct, hθμ]
  have halFil : ∀ w, D.al w ∈ D.Fil := fun w => by
    rw [Datum.Fil, LinearMap.mem_ker, Datum.bb, Datum.al, toLin'_apply, toLin'_apply]
    exact hzero _ _ D.G_mul_F w
  have halbb : ∀ u, D.al (D.bb u) = 0 := fun u => by
    rw [Datum.bb, Datum.al, toLin'_apply, toLin'_apply]
    exact hzero _ _ hFG u

  have hghostA : ∀ n t, (ghostHom p O n) ∘ toA e t = toO e t := fun n t =>
    funext fun i => hofP n _
  have hmem : ∀ r, rowMap D.F e r ∈ latt G := by
    intro r n
    obtain ⟨X, hX⟩ := F_map_ghost D hphi n
    refine ⟨dotLin ((ghostHom p O n ∘ r) ᵥ* X) ∘ₗ (D.Fil.subtype ∘ₗ fil.toLinearMap),
      fun t => ?_⟩
    rw [rowMap_apply, ← ghostHom_apply, RingHom.map_dotProduct]
    have e1 : (ghostHom p O n) ∘ (D.F *ᵥ toA e t) = X *ᵥ D.al (toO e t) := by
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, hghostA, hX, ← mulVec_mulVec, Datum.al,
        toLin'_apply]
    rw [e1, hal, dotProduct_mulVec]
    rfl
  let Φ := (rowMap D.F e).codRestrict (latt G) hmem
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have h1 : ∀ t, r ⬝ᵥ (D.F *ᵥ toA e t) = 0 := fun t =>
      congrArg (fun y : latt G => y.1 t) hr
    have h2 : r ᵥ* D.F = 0 := by
      funext i
      have := h1 (e.symm (Pi.single i 1))
      rw [toA_single, dotProduct_mulVec] at this
      simpa using this
    have h3 : Sandwich.mu ε • r = 0 := by
      have := congrArg (fun z => z ᵥ* D.G) h2
      simp only [vecMul_vecMul, hFG, vecMul_smul, vecMul_one, zero_vecMul] at this
      exact this
    exact (smul_eq_zero.1 h3).resolve_left hμ
  have hsurj : Function.Surjective Φ := by
    intro y
    set s : Fin h → Ainf p O := fun i => y.1 (e.symm (Pi.single i 1)) with hs
    have hy : ∀ t, y.1 t = s ⬝ᵥ toA e t := by
      intro t
      have ht : t = ∑ i, e t i • e.symm (Pi.single i 1) := by
        apply e.injective
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [ht]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [LinearMap.map_smulₛₗ, dotProduct, toA, smul_eq_mul, s]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hdiv : ∀ j, Sandwich.mu ε ∣ (s ᵥ* D.G) j := by
      intro j
      refine _root_.GlobalTheory.GhostKer.mu_dvd_of_ghost p C v O hv ε hε _ fun n => ?_
      obtain ⟨x, hx⟩ := y.2 n
      set gs : Fin h → O := ghostHom p O n ∘ s with hgs
      have hgt : ∀ t, gs ⬝ᵥ toO e t = x (hodgeTate G t) := by
        intro t
        rw [← hx, hy, ← ghostHom_apply, RingHom.map_dotProduct, hghostA]
      have hl : dotLin gs = x ∘ₗ fil.symm.toLinearMap ∘ₗ D.al.codRestrict D.Fil halFil := by
        refine (Pi.basisFun O (Fin h)).ext fun i => ?_
        rw [Pi.basisFun_apply, ← toO_single e i, dotLin_apply, hgt]
        have e2 : D.al.codRestrict D.Fil halFil (toO e (e.symm (Pi.single i 1))) =
            fil (hodgeTate G (e.symm (Pi.single i 1))) := Subtype.ext (hal _)
        simp only [LinearMap.comp_apply, e2, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      have hbb : gs ᵥ* D.G.map (WittVector.fontaineTheta O p) = 0 := by
        funext k
        have e3 := LinearMap.congr_fun hl (D.bb (Pi.single k 1))
        have e4 : D.al.codRestrict D.Fil halFil (D.bb (Pi.single k 1)) = 0 :=
          Subtype.ext (halbb _)
        rw [LinearMap.comp_apply, LinearMap.comp_apply, e4, map_zero, map_zero] at e3
        simp only [dotLin_apply, Datum.bb, toLin'_apply, dotProduct_mulVec] at e3
        simpa using e3
      obtain ⟨Y, hY⟩ := G_map_ghost D hGeq hphi n
      rw [← ghostHom_apply, RingHom.map_vecMul, hY, ← vecMul_vecMul, ← hgs, hbb, zero_vecMul]
      rfl
    choose r hr using hdiv
    have h1 : s ᵥ* D.G = Sandwich.mu ε • r := funext fun j => hr j
    have h2 : r ᵥ* D.F = s := by
      apply smul_right_injective (Fin h → Ainf p O) hμ
      change Sandwich.mu ε • (r ᵥ* D.F) = Sandwich.mu ε • s
      rw [← smul_vecMul, ← h1, vecMul_vecMul, D.G_mul_F, vecMul_smul, vecMul_one]
    refine ⟨r, Subtype.ext (LinearMap.ext fun t => ?_)⟩
    change r ⬝ᵥ (D.F *ᵥ toA e t) = y.1 t
    rw [hy, dotProduct_mulVec, h2]
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun r t => rfl⟩

end GlobalTheory.PDivLat.RowSpace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeMuPInfinityFreeRankOne
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.MuLattice

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] {ε : PreTilt O p}

def muMap (hε : IsPrimitiveSystem ε) (a : Ainf p O) : TDual (PDivGroup.mu p O) where
  toFun t := ofPadic p O ((epsEquiv hε).symm t) * a
  map_add' s t := by rw [map_add (f := _), map_add (f := _), add_mul]
  map_smul' c t := by
    rw [map_smul, smul_eq_mul, map_mul, mul_assoc]; rfl

theorem muMap_apply (hε : IsPrimitiveSystem ε) (a : Ainf p O) (t) :
    muMap hε a t = ofPadic p O ((epsEquiv hε).symm t) * a := rfl

theorem epsEquiv_symm_eps (hε : IsPrimitiveSystem ε) : (epsEquiv hε).symm (epsTate hε) = 1 := by
  rw [LinearEquiv.symm_apply_eq]
  exact (one_smul ℤ_[p] (epsTate hε)).symm

theorem muMap_mem (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0)
    (a : Ainf p O) : muMap hε (Sandwich.mu ε * a) ∈ latt (PDivGroup.mu p O) := fun n =>
  ⟨0, fun t => by
    rw [muMap_apply, ghost_mul, ghost_mul, hμ, zero_mul, mul_zero, LinearMap.zero_apply]⟩

def toLatt (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0) :
    Ainf p O →ₗ[Ainf p O] latt (PDivGroup.mu p O) where
  toFun a := ⟨muMap hε (Sandwich.mu ε * a), muMap_mem hε hμ a⟩
  map_add' a b := by
    ext t
    simp only [muMap_apply, Submodule.coe_add, LinearMap.add_apply]
    ring_nf
  map_smul' c a := by
    ext t
    simp only [muMap_apply, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring_nf

theorem toLatt_eps (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0)
    (a : Ainf p O) : (toLatt hε hμ a).1 (epsTate hε) = Sandwich.mu ε * a := by
  change ofPadic p O ((epsEquiv hε).symm (epsTate hε)) * _ = _
  rw [epsEquiv_symm_eps, map_one, one_mul]

theorem latt_mu_equiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ e : latt (PDivGroup.mu p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, Sandwich.mu ε * e y = y.1 (epsTate hε) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  have hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0 :=
    (_root_.GlobalTheory.PDivLat.ghost_values p C v O hv ε hε).2.2.1
  have hdom := GlobalTheory.ainf_isDomain_and_mu_ne_zero p C v O hv ε (by simpa [zeta] using hε 1)
  haveI := hdom.1
  have hbij : Function.Bijective (toLatt hε hμ) := by
    constructor
    · intro a b hab
      have h := congrArg (fun y : latt (PDivGroup.mu p O) => y.1 (epsTate hε)) hab
      simp only [toLatt_eps] at h
      exact mul_left_cancel₀ hdom.2 h
    · intro y
      have hg : ∀ n, ghost p O n (y.1 (epsTate hε)) = 0 := fun n => by
        obtain ⟨x, hx⟩ := y.2 n
        rw [hx, Subsingleton.elim (hodgeTate (PDivGroup.mu p O) (epsTate hε)) 0, map_zero]
      obtain ⟨a, ha⟩ := _root_.GlobalTheory.GhostKer.mu_dvd_of_ghost p C v O hv ε hε _ hg
      refine ⟨a, Subtype.ext (LinearMap.ext fun t => ?_)⟩
      obtain ⟨c, rfl⟩ := (epsEquiv hε).surjective t
      change ofPadic p O ((epsEquiv hε).symm (epsEquiv hε c)) * (Sandwich.mu ε * a) = y.1 (epsEquiv hε c)
      rw [LinearEquiv.symm_apply_apply, ← ha]
      have hc : epsEquiv hε c = c • epsTate hε := rfl
      rw [hc, LinearMap.map_smulₛₗ, smul_eq_mul]
  refine ⟨(LinearEquiv.ofBijective _ hbij).symm, fun y => ?_⟩
  have h := toLatt_eps hε hμ ((LinearEquiv.ofBijective _ hbij).symm y)
  rw [← h]
  congr 2
  exact (LinearEquiv.ofBijective _ hbij).apply_symm_apply y

end GlobalTheory.MuLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.PointGroup

theorem isIntegrallyClosedIn_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

theorem exists_form (hv : v.Integers O) (G : PDivGroup p O) (ζ : (PDivGroup.mu p O).Tate)
    (hζ : Function.Bijective fun a : ℤ_[p] => a • ζ) :
    ∃ B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p], (∀ s χ, pairing G O s χ = B s χ • ζ) ∧
      Function.Bijective B ∧ Function.Bijective B.flip := by
  haveI := isIntegrallyClosedIn_of_integers hv
  let z := LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ ζ) hζ
  refine ⟨(pairing G O).compr₂ z.symm.toLinearMap, fun s χ => (z.apply_symm_apply _).symm, ?_, ?_⟩
  · exact (LinearEquiv.congrRight (M := G.dual.Tate) z.symm).bijective.comp (G.pairing_bijective C)
  · exact (LinearEquiv.congrRight (M := G.Tate) z.symm).bijective.comp (G.pairing_flip_bijective C)

theorem finite_tate (hv : v.Integers O) (G : PDivGroup p O) : Module.Finite ℤ_[p] G.Tate :=
  haveI := isIntegrallyClosedIn_of_integers hv
  G.finite_tate C

theorem free_tate (hv : v.Integers O) (G : PDivGroup p O) : Module.Free ℤ_[p] G.Tate :=
  haveI := isIntegrallyClosedIn_of_integers hv
  G.free_tate C

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O]
  {ε : PreTilt O p} {hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε}



variable [Algebra ℤ_[p] O]




end GlobalTheory.PointGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpanStatement
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_omega_finite_free_and_p_sq_mem_dlog_span : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), v.Integers O → GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ G : PDivGroup p O, Module.Finite O G.omega ∧ Module.Free O G.omega ∧ ∀ w : G.omega, (p : O) ^ 2 • w ∈ Submodule.span O (Set.range (dlog (G := G))) := by
  first | exact @GlobalTheory.DlogSpan.finite_free_and_sq_smul_mem_span | exact GlobalTheory.DlogSpan.finite_free_and_sq_smul_mem_span | (intros; apply GlobalTheory.DlogSpan.finite_free_and_sq_smul_mem_span <;> assumption)
end

