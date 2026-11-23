module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

variable {p : ℕ} [Fact p.Prime]

structure DPair (G : HTGroup p) where

  β : G.Cˣ

  γ : G.Cˣ

  c : ℚˣ
  sym : sh G β = β
  sim : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β
  reg : (minpoly G.F (γ : G.C)).natDegree = G.n ∧ (minpoly G.F (γ : G.C)).Separable
  trivAf : ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ), Triv G (AfP p) β x t

  posR : ∀ v : InfinitePlace G.F, ∀ x : Fin G.n → ℂ, x ≠ 0 →
    (sigPosH (G.gram_herm v) = 1 → 0 < (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re) ∧
    (sigPosH (G.gram_herm v) ≠ 1 → (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re < 0)

namespace DPair

variable {G : HTGroup p}

def pol (P : DPair G) : Polynomial G.F := minpoly G.F (P.γ : G.C)

def Rel (P Q : DPair G) : Prop :=
  ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧ (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y) ∧ Q.γ = y * P.γ * y⁻¹

def cent (P : DPair G) : Subgroup (G.Cˣ × ℚˣ) where
  carrier := {y | y.1 * P.γ = P.γ * y.1 ∧ (y.1 : G.C) * P.β * sh G y.1 = algebraMap ℚ G.C y.2 * P.β}
  one_mem' := ⟨by simp, by simp [sh]⟩
  mul_mem' := by
    rintro ⟨y, s⟩ ⟨y', s'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, ?_⟩
    · change y * y' * P.γ = P.γ * (y * y')
      change y * P.γ = P.γ * y at h1
      change y' * P.γ = P.γ * y' at h1'
      rw [mul_assoc, h1', ← mul_assoc, h1, mul_assoc]
    · change (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β at h2
      change (y' : G.C) * P.β * sh G y' = algebraMap ℚ G.C s' * P.β at h2'
      change ((y * y' : G.Cˣ) : G.C) * P.β * sh G ((y * y' : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s * s' : ℚˣ) : ℚ) * P.β
      have e : sh G ((y * y' : G.Cˣ) : G.C) = sh G y' * sh G y := by
        simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
      rw [e, Units.val_mul, Units.val_mul, map_mul]
      calc (y : G.C) * y' * P.β * (sh G y' * sh G y) = y * (y' * P.β * sh G y') * sh G y := by
            simp only [mul_assoc]
        _ = algebraMap ℚ G.C s' * (y * P.β * sh G y) := by
            rw [h2']; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
        _ = _ := by rw [h2, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (s' : ℚ)]
  inv_mem' := by
    rintro ⟨y, s⟩ ⟨h1, h2⟩
    change y * P.γ = P.γ * y at h1
    change (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β at h2
    refine ⟨?_, ?_⟩
    · change y⁻¹ * P.γ = P.γ * y⁻¹
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h1, mul_inv_cancel_right]
    · change ((y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * P.β
      have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        simp only [sh]
        rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
      have hs : algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ G.C (s : ℚ) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      calc ((y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y⁻¹ : G.Cˣ) : G.C)
          = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * (((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (s : ℚ) * P.β) *
              sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
            rw [← mul_assoc, ← mul_assoc, ← mul_assoc, Algebra.commutes ((s⁻¹ : ℚˣ) : ℚ), mul_assoc ((y⁻¹ : G.Cˣ) : G.C) _ (algebraMap ℚ G.C (s : ℚ)), hs, mul_one]
        _ = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * ((((y⁻¹ : G.Cˣ) : G.C) * y) * P.β *
              (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
            rw [← h2]; simp only [mul_assoc]
        _ = _ := by rw [Units.inv_mul, e, one_mul, mul_one]

def self (P : DPair G) : P.cent := ⟨(P.γ, P.c), rfl, P.sim⟩

def toAf (P : DPair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) : P.cent →* G.GAf :=
  MonoidHom.codRestrict
    ((((MulAut.conj x).toMonoidHom.comp (Units.map (inC G (AfP p)).toMonoidHom)).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).comp P.cent.subtype) _ fun y => by
      have h := congrArg (inC G (AfP p)) y.2.2
      rw [map_mul, map_mul, map_mul] at h
      have e1 : inC G (AfP p) (sh G y.1.1) = (starT G.star (AfP p) (inC G (AfP p) y.1.1)).unop :=
        (starT_tmul G.star (AfP p) 1 _).symm
      have e2 : inC G (AfP p) (algebraMap ℚ G.C y.1.2) =
          algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) y.1.2) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
      rw [e1, e2] at h
      exact conj_mul_star (starT G.star (AfP p)) (inC G (AfP p) P.β) x
        (Units.map (inC G (AfP p)).toMonoidHom y.1.1) t _ hx h

def atP (P : DPair G) : Gp G := locC G (P.γ, P.c)

def toQr (P : DPair G) (r : ℕ) (z : Gr G r) : P.cent →* Gr G r :=
  ((carry G r z).comp (locC G)).comp P.cent.subtype

def termAt (P : DPair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r) : ℂ :=
  GlobalTheory.LKCount.pointSum (P.toAf x t hx) (P.toQr r z) (sigG G r) Kf K (P.toAf x t hx P.self) δ f φ

def term (P : DPair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  if h : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2 then
    P.termAt Kf f r K φ P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec
      h.choose.1 h.choose.2
  else 0

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
private theorem lkMid_sh_mul_eq_sh_mul_sh_rev (a b : G.C) :
    _root_.GlobalTheory.LKMid.sh G (a * b) =
      _root_.GlobalTheory.LKMid.sh G b * _root_.GlobalTheory.LKMid.sh G a := by
  simp only [_root_.GlobalTheory.LKMid.sh, map_mul, MulOpposite.unop_mul]

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
private theorem lkMid_sh_mul_sh_units_inv_eq_one (y : (G.C)ˣ) :
    _root_.GlobalTheory.LKMid.sh G y *
      _root_.GlobalTheory.LKMid.sh G ((y⁻¹ : (G.C)ˣ) : G.C) = 1 := by
  rw [← lkMid_sh_mul_eq_sh_mul_sh_rev, Units.inv_mul, _root_.GlobalTheory.LKMid.sh_one_eq]


open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
theorem _root_.GlobalTheory.LKDef.DPair.rel_equivalence (G : _root_.GlobalTheory.LKTrip.HTGroup p) :
    Equivalence (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) := by
  refine ⟨fun P => ?_, fun {P₁ P₂} h => ?_, fun {P₁ P₂ P₃} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_, by simp⟩
    simp [_root_.GlobalTheory.LKMid.sh_one_eq]
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_, ?_⟩
    · rw [hβ]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul,
        inv_mul_cancel₀ hs.ne', one_smul]
      simp only [mul_assoc, Units.inv_mul_cancel_left, lkMid_sh_mul_sh_units_inv_eq_one, mul_one]
      rw [mul_inv_cancel₀ hs.ne', one_smul]
    · rw [hγ]; group
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    obtain ⟨y', s', hs', hβ', hγ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_, ?_⟩
    · rw [hβ', hβ, Units.val_mul, lkMid_sh_mul_eq_sh_mul_sh_rev]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
      rw [mul_comm s s']
    · rw [hγ', hγ]; group

theorem pol_eq_of_rel {P Q : DPair G} (h : P.Rel Q) : Q.pol = P.pol := by
  obtain ⟨y, s, _, _, hγ⟩ := h
  have h := minpoly.algEquiv_eq (Pair.innerAlgEquiv G.F y) (P.γ : G.C)
  simp only [pol, hγ, Units.val_mul]
  exact h


open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
theorem _root_.GlobalTheory.LKDef.DPair.mk_eq_iff (P Q : _root_.GlobalTheory.LKDef.DPair G) :
    Quot.mk (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) P = Quot.mk _ Q ↔
      P.Rel Q :=
  ⟨fun h => (_root_.GlobalTheory.LKDef.DPair.rel_equivalence G).eqvGen_iff.mp (Quot.eqvGen_exact h),
    Quot.sound⟩


open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
theorem _root_.GlobalTheory.LKDef.DPair.rel_out (P : _root_.GlobalTheory.LKDef.DPair G) :
    P.Rel
      (Quot.out (Quot.mk (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) P)) :=
  (_root_.GlobalTheory.LKDef.DPair.mk_eq_iff P _).mp (Quot.out_eq _).symm

end DPair

def DCls (G : HTGroup p) : Type := Quot (DPair.Rel (G := G))

def dSumIrr (G : HTGroup p) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : DCls G, if Irreducible (Quot.out q).pol then wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

namespace Example

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example

end Example

end GlobalTheory.LKDef
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IntersectionFamilySymmetric
section
noncomputable section
open ValuativeRel Matrix Polynomial
open scoped Classical

namespace GlobalTheory.DZA

def KO (k : Type) [Field k] [ValuativeRel k] (n : ℕ) : Subgroup (GL (Fin n) k) :=
  (GeneralLinearGroup.map (algebraMap 𝒪[k] k)).range

def K1 {k : Type} [Field k] [ValuativeRel k] {F : Type} [Field F] (rd : 𝒪[k] →+* F) (n : ℕ) : Subgroup (GL (Fin n) k) :=
  (GeneralLinearGroup.map rd).ker.map (GeneralLinearGroup.map (algebraMap 𝒪[k] k))

def infl {k : Type} [Field k] [ValuativeRel k] {F : Type} [Field F] (rd : 𝒪[k] →+* F) {n : ℕ}
    (fb : GL (Fin n) F → ℂ) (x : GL (Fin n) k) : ℂ :=
  if h : ∃ y : GL (Fin n) 𝒪[k], GeneralLinearGroup.map (algebraMap 𝒪[k] k) y = x then
    fb (GeneralLinearGroup.map rd h.choose) else 0

def IsFinNorm {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (δ : GL (Fin n) F') (γ : GL (Fin n) F) : Prop :=
  IsConj (GlobalTheory.LBC.incl F' n γ) (GlobalTheory.LBC.norm F s δ)

def normLift {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (fb : GL (Fin n) F → ℂ) (δ : GL (Fin n) F') : ℂ :=
  if h : ∃ γ, IsFinNorm s δ γ then fb h.choose else 0

def InflMatching : Prop :=
  ∀ (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra k K],
    Continuous (algebraMap k K) → CharZero k →
    ∀ (F F' : Type) [Field F] [Fintype F] [Field F'] [Fintype F'] [Algebra F F'],
      Module.finrank F F' = Module.finrank k K →
    ∀ (rk : 𝒪[k] →+* F) (rK : 𝒪[K] →+* F'), Function.Surjective rk → Function.Surjective rK →
      (∀ (x : 𝒪[k]) (y : 𝒪[K]), (y : K) = algebraMap k K x → rK y = algebraMap F F' (rk x)) →
    ∀ (s : K ≃ₐ[k] K) (sb : F' ≃ₐ[F] F'),
      (∀ x y : 𝒪[K], (y : K) = s x → rK y = sb (rK x)) →
      (∀ z : F', sb z = z ^ Fintype.card F) →
    ∀ (n : ℕ) (fb : GL (Fin n) F → ℂ), (∀ a b, fb (b⁻¹ * a * b) = fb a) →
      (∀ δ : GL (Fin n) K, (GlobalTheory.LBC.norm k s δ : Matrix (Fin n) (Fin n) K).charpoly.Separable →
        ∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k K) =
            (GlobalTheory.LBC.norm k s δ : Matrix (Fin n) (Fin n) K).charpoly →
          GlobalTheory.BCT.twOrb (GlobalTheory.LBC.galAct s n) (KO K n) δ (infl rK (normLift sb fb)) =
            GlobalTheory.BCT.twOrb (MonoidHom.id _) (KO k n) γ (infl rk fb)) ∧
      (∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable →
        GlobalTheory.BCT.twOrb (MonoidHom.id _) (KO k n) γ (infl rk fb) ≠ 0 →
          ∃ δ : GL (Fin n) K, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k K) =
            (GlobalTheory.LBC.norm k s δ : Matrix (Fin n) (Fin n) K).charpoly)

end GlobalTheory.DZA
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory.Cartier

namespace GlobalTheory.LogDR

section Algebra

abbrev abelian₂ (K : Type) [Field K] : Type := ExteriorAlgebra K Ω[K⁄ℤ]

variable {K : Type} [Field K]

abbrev dK (f : K) : Ω[K⁄ℤ] := KaehlerDifferential.D ℤ K f


variable (K) in
def extD : abelian₂ K →+ abelian₂ K := (CechDR.dDR ℤ K).toAddMonoidHom

theorem extD_apply (η : abelian₂ K) : extD K η = CechDR.dDR ℤ K η := rfl

def dlog (g : Kˣ) : Ω[K⁄ℤ] := ((g⁻¹ : Kˣ) : K) • dK (g : K)

def spanForms (M : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ) : AddSubgroup (abelian₂ K) :=
  AddSubgroup.closure
    {η | ∃ c ∈ M, ∃ v : Fin a → Ω[K⁄ℤ], (∀ i, v i ∈ H) ∧ η = c • ExteriorAlgebra.ιMulti K a v}

def frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) : Ω[K⁄ℤ] :=
  if i ∈ J then dlog (x i) else dK (x i : K)

def logWedge {n : ℕ} (x : Fin n → Kˣ) (I : Finset (Fin n)) : abelian₂ K :=
  ((I.sort (· ≤ ·)).map fun i => ExteriorAlgebra.ι K (dlog (x i))).prod

def chartForms (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) :
    AddSubgroup (abelian₂ K) :=
  spanForms {c | c * t ∈ A} (Set.range (frame x J)) a

def IsCoord {n : ℕ} (x : Fin n → Kˣ) : Prop :=
  LinearIndependent K (fun i => dK (x i : K)) ∧
    Submodule.span K (Set.range fun i => dK (x i : K)) = ⊤

structure AlgChart (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) : Prop where

  mem : ∀ i, (x i : K) ∈ A

  coord : IsCoord x

  deriv : ∀ f ∈ A, ∃ c : Fin n → K, (∀ i, c i ∈ A) ∧ dK f = ∑ i, c i • dK (x i : K)

  root : ∀ (S : Finset (Fin n)) (g : K) (m : ℕ), 0 < m →
    g ^ m / ∏ j ∈ S, (x j : K) ∈ A → g / ∏ j ∈ S, (x j : K) ∈ A

def IsCartierMap (p : ℕ) {n : ℕ} (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K) : Prop :=
  (∀ c : K, γ (algebraMap K (abelian₂ K) c) = algebraMap K (abelian₂ K) (c ^ p)) ∧
    ∀ i, γ (ExteriorAlgebra.ι K (dlog (x i))) = ExteriorAlgebra.ι K (dlog (x i))

def IsEulerContraction {n : ℕ} (x : Fin n → Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K) : Prop :=
  θ 1 = 0 ∧ (∀ (v : Ω[K⁄ℤ]) (η : abelian₂ K),
    θ (ExteriorAlgebra.ι K v * η) = θ (ExteriorAlgebra.ι K v) * η - ExteriorAlgebra.ι K v * θ η) ∧
    ∀ j, θ (ExteriorAlgebra.ι K (dlog (x j))) = if j = i then 1 else 0

end Algebra

section Scheme

variable {X : Scheme.{0}} [IsIntegral X]

def locRing (y : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk y) X.functionField).range

theorem mem_locRing {y : X} {f : X.functionField} : f ∈ locRing y ↔ RegAt y f := Iff.rfl

def LogUnit (Z : Set X) (y : X) (g : X.functionFieldˣ) : Prop :=
  ∀ z : X, z ⤳ y → z ∉ Z → UnitAt z (g : X.functionField)

def logAt (Z : Set X) (G : CartierDiv X) (a : ℕ) (y : X) : AddSubgroup (abelian₂ X.functionField) :=
  spanForms {c | G.RegularAt y c} (dlog '' {g | LogUnit Z y g}) a


omit [IsIntegral X] in
def latSec {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) (U : X.Opens) : AddSubgroup V :=
  ⨅ y ∈ U, M y

abbrev logSec (Z : Set X) (G : CartierDiv X) (a : ℕ) (U : X.Opens) :
    AddSubgroup (abelian₂ X.functionField) :=
  latSec (logAt Z G a) U

structure IsLogChart (Z : Set X) (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ)
    (J : Finset (Fin n)) : Prop where

  chart : ∀ y ∈ U, AlgChart (locRing y) x

  logUnit : ∀ y ∈ U, ∀ g : X.functionFieldˣ, LogUnit Z y g ↔
    ∃ (u : X.functionFieldˣ) (m : Fin n → ℤ), UnitAt y (u : X.functionField) ∧ g = u * ∏ j ∈ J, x j ^ m j

def IsSncOn {C : Type} (E : C → CartierDiv X) (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ)
    (J : Finset (Fin n)) : Prop :=
  ∃ e : C → Option (Fin n), (∀ c c' j, e c = some j → e c' = some j → c = c') ∧
    (∀ j, j ∈ J ↔ ∃ c, e c = some j) ∧
    ∀ c, ∀ y ∈ U, (E c).IsEqn y ((e c).elim 1 x)

def suppAll {C : Type} (E : C → CartierDiv X) : Set X := ⋃ c, ((E c).supp : Set X)

structure SncAtlas {C : Type} (E : C → CartierDiv X) (n : ℕ) (ι : Type) where

  U : ι → X.Opens

  x : ι → Fin n → X.functionFieldˣ

  J : ι → Finset (Fin n)

  affine : ∀ i, IsAffineOpen (U i)

  gen : ∀ i, genericPoint X ∈ U i

  cover : ⨆ i, U i = ⊤

  chart : ∀ i, IsLogChart (suppAll E) (U i) (x i) (J i)

  snc : ∀ i, IsSncOn E (U i) (x i) (J i)

structure LatModel {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V)
    (F : X.Modules) where

  val : ∀ U : X.Opens, genericPoint X ∈ U → (Γ(F, U) →+ V)

  inj : ∀ U h, Function.Injective (val U h)

  range : ∀ U h, (val U h).range = latSec M U

  res : ∀ (U W : X.Opens) (e : W ≤ U) (h : genericPoint X ∈ W) (s : Γ(F, U)),
    val W h (F.presheaf.map (homOfLE e).op s) = val U (e h) s

  smul : ∀ U h (r : Γ(X, U)) (s : Γ(F, U)), val U h (r • s) = fnOf U h r • val U h s

end Scheme

end GlobalTheory.LogDR
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped TensorProduct

namespace GlobalTheory.ResW

def blkE {r s N : ℕ} (h : r + s = N) : Fin r ⊕ Fin s ≃ Fin N := finSumFinEquiv.trans (finCongr h)

def blkM (R : Type) [CommRing R] {r s N : ℕ} (h : r + s = N) :
    Matrix (Fin r) (Fin r) R × Matrix (Fin s) (Fin s) R →* Matrix (Fin N) (Fin N) R where
  toFun p := Matrix.reindex (blkE h) (blkE h) (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def blk {R : Type} [CommRing R] {r s N : ℕ} (h : r + s = N) : GL (Fin r) R × GL (Fin s) R →* GL (Fin N) R :=
  (Units.map (blkM R h)).comp MulEquiv.prodUnits.symm.toMonoidHom

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N r s m a : ℕ}


variable (E) in
def nu (t : ℝ) : HChar E := GlobalTheory.HeckeGal.Model.absPow E t





section Passive

variable {M : Type} [AddCommGroup M] [Module ℂ M]

end Passive


variable (E) in
abbrev Letter : Type := Σ a : ℕ, CuspSub E a

def wsize (u : List (Letter E)) : ℕ := (u.map (·.1)).sum

noncomputable def Vec : List (Letter E) → Type
  | [] => PUnit
  | x :: u => x.2.V × Vec u


variable (E N) in
def zc : Module.End ℂ (Sm E N) := lie E N fun i j => if i = j then 1 else 0

def cex (x : Letter E) : ℂ := Classical.epsilon fun c : ℂ => ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ

def rexp (x : Letter E) : ℝ := (cex x).re / (x.1 * Module.finrank ℚ E)

def tw (x : Letter E) (t : ℝ) : Letter E := ⟨x.1, x.2.twist (nu E t)⟩

def SatVec (φ : Sm E N) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop :=
  ∀ᶠ v in Filter.cofinite, GlobalTheory.LFun.IsSatVecGL v ((finRep E N).comp (locGL E N v)) φ (B v)

def SatFam (V : Submodule ℂ (Sm E N)) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop := ∀ φ ∈ V, φ ≠ 0 → SatVec φ B


end GlobalTheory.ResW

end
end

