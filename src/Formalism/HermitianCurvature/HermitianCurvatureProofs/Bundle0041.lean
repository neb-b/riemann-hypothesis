module

public import Formalism.HermitianCurvature.Bundle0008
public import Formalism.HermitianCurvature.StatementNF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0038

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CommonEigenvectors
section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CommonEigenvectors

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem eig_in [FiniteDimensional ℂ V] (T : Module.End ℂ V) (G : Submodule ℂ V) (hG : G ≠ ⊥)
    (hT : ∀ x ∈ G, T x ∈ G) : ∃ (μ : ℂ) (x : V), x ∈ G ∧ x ≠ 0 ∧ T x = μ • x := by
  haveI : Nontrivial G := Submodule.nontrivial_iff_ne_bot.2 hG
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (T.restrict hT)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, x, x.2, fun h => hx.2 (Subtype.ext h), ?_⟩
  have h1 := Module.End.mem_eigenspace_iff.1 hx.1
  have h2 := congrArg Subtype.val h1
  simpa using h2

theorem common [FiniteDimensional ℂ V] {ι : Type} [DecidableEq ι] (D : ι → Module.End ℂ V)
    (hc : ∀ a b, D a * D b = D b * D a) (s : Finset ι) (G : Submodule ℂ V) (hG : G ≠ ⊥)
    (hst : ∀ a, ∀ x ∈ G, D a x ∈ G) :
    ∃ (G' : Submodule ℂ V) (ν : ι → ℂ), G' ≤ G ∧ G' ≠ ⊥ ∧ (∀ a, ∀ x ∈ G', D a x ∈ G') ∧
      ∀ a ∈ s, ∀ x ∈ G', D a x = ν a • x := by
  induction s using Finset.induction_on with
  | empty => exact ⟨G, 0, le_rfl, hG, hst, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨G₁, ν, h1, h2, h3, h4⟩ := ih
    obtain ⟨μ, x, hx1, hx2, hx3⟩ := eig_in (D a) G₁ h2 (h3 a)
    refine ⟨G₁ ⊓ LinearMap.ker (D a - μ • 1), Function.update ν a μ, le_trans inf_le_left h1, ?_, ?_, ?_⟩
    · intro hbot
      apply hx2
      have hm : x ∈ G₁ ⊓ LinearMap.ker (D a - μ • 1) :=
        Submodule.mem_inf.2 ⟨hx1, LinearMap.mem_ker.2 (by simp [hx3])⟩
      rw [hbot] at hm
      simpa using hm
    · intro c y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      have hy2' : D a y = μ • y := by simpa [sub_eq_zero] using LinearMap.mem_ker.1 hy2
      have hcomm : D a (D c y) = D c (D a y) := by
        have := congrArg (fun T => T y) (hc a c)
        simpa using this
      exact Submodule.mem_inf.2 ⟨h3 c y hy1, LinearMap.mem_ker.2 (by simp [hcomm, hy2'])⟩
    · intro b hb y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      have hy2' : D a y = μ • y := by simpa [sub_eq_zero] using LinearMap.mem_ker.1 hy2
      rcases Finset.mem_insert.1 hb with rfl | hb
      · simp [hy2']
      · have hba : b ≠ a := fun h => ha (h ▸ hb)
        simp [Function.update_apply, hba, h4 b hb y hy1]

def hop {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V :=
  ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) • E c c

theorem diag_move {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (c a b : Fin n) (x : V) :
    E c c (E a b x) = E a b (E c c x) + ((if c = a then E a b x else 0) - (if b = c then E a b x else 0)) := by
  have h : E c c (E a b x) - E a b (E c c x) = ((if c = a then E c b else 0) - (if b = c then E a c else 0)) x :=
    congrArg (fun T => T x) (hE c c a b)
  rw [sub_eq_iff_eq_add'] at h
  rw [h, LinearMap.sub_apply]
  congr 1
  split_ifs <;> subst_vars <;> simp

theorem hop_move {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) (x : V) :
    hop E (E a b x) = E a b (hop E x) + (((b : ℕ) : ℂ) - ((a : ℕ) : ℂ)) • E a b x := by
  unfold hop
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, diag_move hE, smul_add, smul_sub,
    smul_ite, smul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [← sub_smul]
  congr 2
  ring

theorem hop_weight {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {θ : Fin n → ℂ} {x : V}
    (hx : ∀ a, E a a x = θ a • x) :
    hop E x = (∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * θ c) • x := by
  unfold hop
  rw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearMap.smul_apply, hx, smul_smul]

theorem hval_re {n : ℕ} (θ : Fin n → ℂ) :
    (∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * θ c).re = hval θ := by
  unfold hval
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun c _ => by simp [Complex.mul_re]

end Formalism.FourierDecayAlt.P.CommonEigenvectors

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr CommonEigenvectors

theorem exists_singular_maximal_vector : Qr.ExistsSingMax := by
  intro V _ _ _ n E hE S hS hS0
  have hcomm : ∀ a b : Fin n, E a a * E b b = E b b * E a a := by
    intro a b
    have h := hE a a b b
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  have hstab : ∀ a b, ∀ x ∈ S, E a b x ∈ S := by
    intro a b x hx
    exact hS a b x hx
  obtain ⟨G', ν0, hG'S, hG'0, -, hG'ν⟩ :=
    common (fun a => E a a) hcomm Finset.univ S hS0 (fun a => hstab a a)
  obtain ⟨x0, hx0G, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hG'0
  let W : Set (Fin n → ℂ) := {θ | ∃ x ∈ S, x ≠ 0 ∧ ∀ a, E a a x = θ a • x}
  have hWne : W.Nonempty := ⟨ν0, x0, hG'S hx0G, hx00, fun a => hG'ν a (Finset.mem_univ a) x0 hx0G⟩
  have hWfin : W.Finite := by
    refine (Set.Finite.pi (t := fun a => {μ | (E a a).HasEigenvalue μ})
      fun a => Module.End.finite_hasEigenvalue (E a a)).subset ?_
    rintro θ ⟨x, -, hx0, hx⟩
    exact Set.mem_univ_pi.2 fun a =>
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hx a), hx0⟩
  obtain ⟨ν, ⟨v, hvS, hv0, hv⟩, hmax⟩ := Set.exists_max_image W hval hWfin hWne
  refine ⟨ν, v, hvS, hv0, ⟨hv, fun a b hab => ?_⟩, fun θ x hxS hx0 hx => hmax θ ⟨x, hxS, hx0, hx⟩⟩
  by_contra hy
  set y := E a b v with hydef
  have hyS : y ∈ S := hstab a b v hvS
  let θ' : Fin n → ℂ := fun c => ν c + ((if c = a then 1 else 0) - (if b = c then 1 else 0))
  have hy' : ∀ c, E c c y = θ' c • y := by
    intro c
    rw [hydef, diag_move hE, hv c, map_smul]
    simp only [θ', add_smul, sub_smul, ite_smul, one_smul, zero_smul]
  have hle := hmax θ' ⟨y, hyS, hy, hy'⟩
  have k1 := hop_weight hy'
  have k2 := hop_move hE a b v
  rw [hop_weight hv, map_smul, ← hydef, ← add_smul, k1] at k2
  have k3 := smul_left_injective ℂ hy k2
  have hv' : hval θ' = hval ν + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    rw [← hval_re, ← hval_re, k3]
    simp
  have hba : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by
    have := Fin.lt_iff_val_lt_val.1 hab
    exact_mod_cast this
  linarith

attribute [local instance 100] LieRing.ofAssociativeRing in
theorem singular_dominant : Qr.SingDom := by
  intro V _ _ _ n E ν v hE hv hv0 a b hab
  obtain ⟨hd, hr⟩ := hv
  have hab' : a ≠ b := ne_of_lt hab
  by_cases h0 : E a a - E b b = 0
  · refine ⟨0, ?_⟩
    have h1 : (E a a - E b b) v = 0 := by rw [h0]; rfl
    rw [LinearMap.sub_apply, hd, hd, ← sub_smul] at h1
    simpa [hv0] using h1
  · have e0 := hE a b b a
    have e1 := hE a a a b
    have e2 := hE b b a b
    have e3 := hE a a b a
    have e4 := hE b b b a
    simp [hab', hab'.symm] at e0 e1 e2 e3 e4
    have t : IsSl2Triple (E a a - E b b) (E a b) (E b a) :=
      { h_ne_zero := h0
        lie_e_f := by rw [Ring.lie_def, e0]
        lie_h_e_nsmul := by
          rw [Ring.lie_def]
          calc (E a a - E b b) * E a b - E a b * (E a a - E b b)
              = (E a a * E a b - E a b * E a a) - (E b b * E a b - E a b * E b b) := by noncomm_ring
            _ = 2 • E a b := by rw [e1, e2]; abel
        lie_h_f_nsmul := by
          rw [Ring.lie_def]
          calc (E a a - E b b) * E b a - E b a * (E a a - E b b)
              = (E a a * E b a - E b a * E a a) - (E b b * E b a - E b a * E b b) := by noncomm_ring
            _ = -(2 • E b a) := by rw [e3, e4]; abel }
    have pv : t.HasPrimitiveVectorWith v (ν a - ν b) :=
      { ne_zero := hv0
        lie_h := by
          show (E a a - E b b) v = (ν a - ν b) • v
          rw [LinearMap.sub_apply, hd, hd, sub_smul]
        lie_e := by
          show E a b v = 0
          exact hr a b hab }
    exact pv.exists_nat

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def BuiltOW (Cc : ℝ) (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) : Prop :=
  JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ ∧ (∀ v, (S.G.place (S.pl v)).Ok) ∧
    Sz.IsWord S.G.k S.de ∧ Sz.IsWord S.G.k S.de'

def lamCfg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ :=
  fun s => (S.G.place (S.pl v)).lam ((s : ℕ) + 1)

def OmP (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) : Set (B.Mat S.G.k S.G.r) :=
  {g | 0 < Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g ∧
    ∀ a : Fin S.G.r, Formalism.QuantumDeterminants.Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def trJ (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT :=
  fun ρ => MA.toSm (D.parOf S v) fun q =>
    ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq (T v).base q.1)))

def IsFrame (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | (D.parOf S v).TT < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, (D.parOf S v).TT < Complex.normSq ζ →
    (∀ ρ, e ρ ζ ∈ NF.Fib S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec (T v).base.π (T v).base.π' ζ) ∧
    (∀ ρ ρ', inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e ρ' ζ)) = if ρ = ρ' then (1 : ℂ) else 0) ∧
    ∀ X ∈ NF.Fib S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec (T v).base.π (T v).base.π' ζ,
      X = ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ

def IsGauge (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ Y : ℝ,
    trJ S T v e (Q.CV S.G.k S.G.r (Y : ℂ) J) =
      MA.actA (D.parOf S v) (Wd.C0 (MA.QQr (D.parOf S v) (MA.DQ (D.parOf S v))) (MA.sites (D.parOf S v) (MA.DQ (D.parOf S v))) (Y : ℂ))
        (trJ S T v e J)

end defs

def LamCfgInterlaces : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    2 ≤ S.G.k → (∀ v, (S.G.place (S.pl v)).Ok) → Sz.IsWord S.G.k S.de → Sz.IsWord S.G.k S.de' → ∀ v,
      C7.LamInterlaces S.G.k S.G.r (D.parOf S v).u (lamCfg S v) ∧
        C7.LamInterlaces S.G.k S.G.r (D.parOf S v).u' (lamCfg S v)

def AdmInCut : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    C.GridsOK S → ∀ v (a : List C.Letter), D.AdmAt S v a → ∀ x ∈ a, x.2 ∈ Set.Icc (S.cutLo v) (S.cutHi v)

def CVPresFF : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v, ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ (Y : ℝ) (s : ℂ), s • Q.CV S.G.k S.G.r (Y : ℂ) J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)

def BesselEigen : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v, ∀ Y : ℝ, ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
      Q.CV S.G.k S.G.r (Y : ℂ) (B.JF (T v).base (f v)) (B.gq (T v).base x) =
        ((S.P v Y : ℝ) : ℂ) • B.JF (T v).base (f v) (B.gq (T v).base x)

def EnergyTr : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      (∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ (Y : ℝ) (s : ℂ), s • Q.CV S.G.k S.G.r (Y : ℂ) J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) →
      ∀ ε : ℝ, 0 < ε → B.JF (T v).base (D.cutF (T v).base χ (f v) ε) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) → ∀ a : List C.Letter, D.AdmAt S v a →
        C7.principalHermitianLattice (T v).base (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε) =
          MA.ipA (D.parOf S v)
            (trJ S T v e (a.reverse.foldr (fun x J => (M.sgn (D.parOf S v) (S.l + 1)) • Q.CV S.G.k S.G.r (x.2 : ℂ) J)
              (B.JF (T v).base (D.cutF (T v).base χ (f v) ε))))
            (trJ S T v e (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)))

def CutTr : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) → ∀ c : LE.Cut, c.χ = χ → ∀ ε : ℝ, 0 < ε →
        trJ S T v e (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)) =
          MA.chiJ (D.parOf S v) (trJ S T v e (B.JF (T v).base (f v))) c ε

def EnergyReal : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v, ∀ ε : ℝ, 0 < ε → ∀ a : List C.Letter, D.AdmAt S v a →
      (C7.principalHermitianLattice (T v).base (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε)).im = 0

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExponentWordRecursion
section
open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.ListSumInequalities

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma list_sum_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (f : α → List β) (h : β → M) :
    ((L.flatMap f).map h).sum = (L.map fun a => ((f a).map h).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

lemma norm_list_sum_le {α : Type*} (L : List α) (f : α → E) :
    ‖(L.map f).sum‖ ≤ (L.map fun a => ‖f a‖).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

lemma list_sum_le {α : Type*} (L : List α) (f f' : α → ℝ) (h : ∀ a ∈ L, f a ≤ f' a) :
    (L.map f).sum ≤ (L.map f').sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

lemma list_sum_nonneg {α : Type*} (L : List α) (f : α → ℝ) (h : ∀ a ∈ L, 0 ≤ f a) : 0 ≤ (L.map f).sum := by
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact h a ha)

end Formalism.FourierDecayAlt.P.ListSumInequalities

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JConvOfJDom
section
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jConv_of_jDom : Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.JF.JConv := by
  intro hD k r Wp Wq _ _ _ _ _ _ D A F hT hC
  obtain ⟨hmeas, hbd⟩ := hD k r Wp Wq D A 0 F hT hC
  have hx : Continuous (fun p : SS k r => xiP D p) := by
    clear hmeas hbd hD hT hC
    unfold xiP psi ell
    refine Continuous.mul ?_ (Continuous.star ?_)
    · refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun a _ => ?_)))))
      split_ifs
      · simp only [Matrix.of_apply]; fun_prop
      · simp only [Matrix.of_apply, Matrix.mulVec, dotProduct]; fun_prop
    · refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun a _ => ?_)))))
      split_ifs
      · simp only [Matrix.of_apply]; fun_prop
      · simp only [Matrix.of_apply, Matrix.mulVec, dotProduct]; fun_prop
  have h0 : (0 : ℕ) + 0 ≤ 0 := le_rfl
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨b, hb, hbb⟩ := hbd {g} isCompact_singleton (Set.singleton_subset_iff.mpr hg)
    have hbg := hbb [] [] (by simp) (by simp) h0 g (Set.mem_singleton g)
    have hm := hmeas [] [] (by simp) (by simp) h0 g hg
    refine Integrable.mono' hb (hx.aestronglyMeasurable.smul hm) ?_
    filter_upwards [hbg] with p hp
    calc ‖xiP D p • rho D p F g‖ = ‖xiP D p‖ * ‖rho D p F g‖ := norm_smul _ _
      _ ≤ 1 * ‖rho D p F g‖ := by gcongr; exact SmoothnessOnGoodSet.norm_xiP D p
      _ = ‖rho D p (dLR (List.map (AdL p) []) (List.map (AdR p) []) F) g‖ := by rw [one_mul]; rfl
      _ ≤ b p := hp
  · intro K hK hKO
    obtain ⟨b, hb, hbb⟩ := hbd K hK hKO
    exact ⟨b, hb, fun g hg => hbb [] [] (by simp) (by simp) h0 g hg⟩

end Formalism.FourierDecayAlt.P.JFxDs1
end
end

