module

public import Formalism.LocalToGlobal.Columns.Bundle0030
public import Mathlib
public import Formalism.LocalToGlobal.Columns.Bundle0029
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.ChainCounts
public import Formalism.LocalToGlobal.Columns.Bundle0018
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant
public import Formalism.LocalToGlobal.Divisibility.Bundle0002
public import Formalism.LocalToGlobal.Columns.ChainOneB
public import Formalism.LocalToGlobal.Columns.Record
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
public import Formalism.LocalToGlobal.Columns.Bundle0008
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0013
public import Formalism.LocalToGlobal.Columns.RecChainCUnfPol

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.DecoratedFrameDiagonalTwistDecoration
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Fr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.SameOn (B : Finset (HeightOneSpectrum (𝓞 E))) (d d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : Prop := ∀ P ∈ B, d'.1.at P = d.1.at P

def DecoF.repl (p : DecoF E n ST SG Q) (d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (h : DecoSet.SameOn Q p.deco d') : DecoF E n ST SG Q :=
  ⟨(d', p.1.2), fun P x => by rw [h P.1 P.2]; exact p.2 P x⟩


open Classical in
def DecoF.mv (p : DecoF E n ST SG Q) (d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : DecoF E n ST SG Q :=
  if h : DecoSet.SameOn Q p.deco d' then p.repl d' h else p

theorem DecoF.mv_pos {p : DecoF E n ST SG Q} {d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (h : DecoSet.SameOn Q p.deco d') : p.mv d' = p.repl d' h := by
  unfold DecoF.mv; rw [dite_eq_left h]

theorem DecoF.mv_deco {p : DecoF E n ST SG Q} {d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (h : DecoSet.SameOn Q p.deco d') : (p.mv d').deco = d' := by
  rw [DecoF.mv_pos h]; rfl

theorem DecoSet.sameOn_up {B : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1)
    (hB : ∀ P' ∈ B, P' ≠ P.1 ∧ P' ≠ conjPrime₂ P.1) (q : 𝓞 E) {x : Sp E n} (hx : x ∈ d.1.N) : DecoSet.SameOn B d (d.up P q x) := by
  intro P' hP'
  unfold DecoSet.up
  split_ifs with hok
  · show localization₂ P'.asIdeal (upN P.1.asIdeal d.1.N x) = localization₂ P'.asIdeal d.1.N
    exact ((upN_spec d.2.lat d.2.uni P.1 hne hx).2.2.1 P' (hB P' hP').1 (hB P' hP').2).localization_eq
  · rfl

end Fr

section Yb

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem locLat_sameAt {E : Type} [Field E] [NumberField E] {n : ℕ} (SB : Finset (HeightOneSpectrum (𝓞 E))) {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : ∀ P ∈ SB, localization₂ P.asIdeal N' = localization₂ P.asIdeal N) (e : SB → ℤ) : locLat SB N' e = locLat SB N e := by
  unfold locLat
  exact iInf_congr fun P => by rw [h P.1 P.2]

theorem ybSet_sameAt {n : ℕ} {N N' : Submodule (𝓞 X.E) (Sp X.E n)} (h : ∀ P ∈ rowSG Pr sel mu, localization₂ P.asIdeal N' = localization₂ P.asIdeal N) :
    ybSet sel mu cst N' = ybSet sel mu cst N := by
  unfold ybSet
  rw [locLat_sameAt _ h, locLat_sameAt _ h]

end Yb

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.DetChrJoint
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

section Joint

open Classical

variable {X : Fields} {Pr : Primes X}

theorem conjP_vGs (hX : X.Ok) (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) :
    HeckeExHost.conjPrime₂ P ≠ P ∧ HeckeExHost.conjPrime₂ P ∉ Pr.vGs := by
  have hmem : ∀ j, P ∈ Pr.vG j → X.conjO (Pr.piG j) ∈ P.asIdeal := fun j h => ChainCounts.mem_of_mem_divs h
  have hcomap : ∀ y : 𝓞 X.E, y ∈ (HeckeExHost.conjPrime₂ P).asIdeal ↔ X.conjO y ∈ P.asIdeal := fun y => Iff.rfl
  have hcop : ∀ j, Pr.piG j ∈ P.asIdeal → X.conjO (Pr.piG j) ∈ P.asIdeal → False := by
    intro j h1 h2
    obtain ⟨a, b, hab⟩ := hPr.piG_cop j
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
  obtain ⟨i, hi⟩ : ∃ i, P ∈ Pr.vG i := by
    rcases Finset.mem_union.1 hP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : Pr.piG i ∈ (HeckeExHost.conjPrime₂ P).asIdeal := (hcomap _).2 (hmem i hi)
    rw [h] at h1
    exact hcop i h1 (hmem i hi)
  · obtain ⟨j, hj⟩ : ∃ j, HeckeExHost.conjPrime₂ P ∈ Pr.vG j := by
      rcases Finset.mem_union.1 h with h' | h'
      · exact ⟨0, h'⟩
      · exact ⟨1, h'⟩
    have h1 : Pr.piG j ∈ P.asIdeal := by
      have := (hcomap _).1 (ChainCounts.mem_of_mem_divs hj)
      rwa [HeckeExHost.conjO_conjO'] at this
    by_cases hij : j = i
    · subst hij
      exact hcop j h1 (hmem j hi)
    · have hg1 : ((Pr.g j : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm j]
        exact Ideal.mul_mem_right _ _ h1
      have hg2 : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm i]
        exact Ideal.mul_mem_left _ _ (hmem i hi)
      have hne : Pr.g j ≠ Pr.g i := by
        have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
        rcases key j i hij with ⟨h0, h1'⟩ | ⟨h0, h1'⟩
        · rw [h0, h1']; exact hPr.g_ne
        · rw [h0, h1']; exact hPr.g_ne.symm
      have hcopZ : Nat.Coprime (Pr.g j) (Pr.g i) := (Nat.coprime_primes (hPr.g_prime j) (hPr.g_prime i)).2 hne
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (Pr.g j : ℤ) + b * (Pr.g i : ℤ) = 1 := by
        refine ⟨Nat.gcdA (Pr.g j) (Pr.g i), Nat.gcdB (Pr.g j) (Pr.g i), ?_⟩
        have := Nat.gcd_eq_gcd_ab (Pr.g j) (Pr.g i)
        rw [hcopZ] at this
        push_cast at this
        linarith
      apply P.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 X.E) = (a : 𝓞 X.E) * ((Pr.g j : ℕ) : 𝓞 X.E) + (b : 𝓞 X.E) * ((Pr.g i : ℕ) : 𝓞 X.E) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 X.E)) hab
        push_cast at this
        exact this.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ hg1) (Ideal.mul_mem_left _ _ hg2)

end Joint

section Core

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks}

end Core

end DetChrL

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.OcbBEntEntB
section
noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def ocbBEnt {E : Type} [Field E] {N' N : ℕ} (n' n q : ℕ) (y : HomE E N' N) (l s : ℕ) : E :=
  Loc.atN (y (Loc.eN E N' s)) l * (q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l)

theorem ocbBEnt_entB {E : Type} [Field E] [NumberField E] {N' N : ℕ} (q k₀ c' n' c n : ℕ) (y : HomE E N' N) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) y p p' = ocbBEnt n' n q y (LocE.fIdx k₀ c n p) (LocE.fIdx k₀ c' n' p') := rfl

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RecChainYKmap
section
open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col.Sc

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker Formalism.L2.Col

section Charts

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev SecY (u : Pr.Word) (m2 : ℕ) : Type := ∀ j b, ((Formalism.L2.Col.chFY W sel mu cst L u m2 j).mem b).Sec

variable {W sel mu cst L}

variable {Ch}

end Charts

end Formalism.L2.Col.Sc
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Eq

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (Am : Amb X) (u : Pr.Word)

def oneAl (j : ℕ) (h : j ≤ m2 + 1) : (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).β j := ⟨(), h⟩

variable {Λ sel mu}

variable (Λ sel mu)

def FixE : Prop :=
  ∀ h ∈ (Λ (m2 + 1)).grp, ∀ w : Pr.vGs,
    ((h w : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal)) : Matrix _ _ (𝓞 X.E ⧸ w.1.asIdeal)).mulVec (Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k) =
      Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k

variable {W Λ Ch sel mu cst hQ m2 Am u}

end Eq

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ResidueFieldUnfoldingClaimsHold
section
namespace Formalism.L2.Col

theorem residueFieldUnfolding_claims_hold : ResidueFieldUnfoldingSupport ∧ ResidueFieldUnfoldingNonzero := by
  refine ⟨?_, ?_⟩
  · intro k _ _ ψ₀ χ k₀ m t j n' c n _ hr h hne
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    exact (support_oneCoset k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).1 h hne
  · intro k _ _ ψ₀ χ k₀ m t j n' c n _ hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    exact (support_oneCoset k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).2

end Formalism.L2.Col
end

-- bundled from Formalism.LocalToGlobal.Columns.StabMapRLInjective
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section XpL

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Λm : LevFam X.E X.K (R.N R.m) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG')
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

@[reducible] def topGSD (u : Pr.Word) : GSD X.K := formGSD (colVal W u R.m (Pr.vT u) Pr.vGs) Λm

variable {W ΛM}


variable {Λm}



end XpL

section XpC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R) (bm : Λ.β R.m)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG')
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

variable {W Λ bm ΛM}





end XpC

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ₀ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

end One

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQDCls
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QCls

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}


variable (ST SG Q) in
def FrExists : Prop :=
  ∀ (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : Q), ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ y, f y ∈ d.1.at P.1 ↔ y ∈ stdAt E n P.1

theorem qdf_toGLm_ratHom (γ : URat hc n) : toGLm E n (ratHom hc n γ).1 = (γ : GL (Fin n) E) := by
  simp [toGLm, ratHom, Formalism.UG.glEquiv]

variable (H : Subgroup (GLG (E := E) (n := n) (SG := SG)))

theorem qdf_rel_of_orbit (q : QLoc hc n Q Θ) {x x' : UAd hc n} {p : DecoF E n ST SG Q} (a : UF E n × H × Θ.grp)
    (hx : FrOver q x.1 p) (hx' : FrOver q x'.1 (a • p)) :
    ∃ (γ : URat hc n) (κ : levUQ hc n ST SG Q H q), ratHom hc n γ = a.1 ∧
      (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
        (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
  have hd : decoOf ST SG (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((a.1, a.2.1) : UF E n × H) • decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [hx'.1, hx.1]; rfl
  obtain ⟨γ, k, h1, -, e⟩ := rlc_rel_of_orbit hc n ST SG H (a.1, a.2.1) hd
  have hkQ : ∀ P : Q, q.at P (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ q.U P := by
    intro P
    have hke : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      rw [e]; group
    have hA := hx'.2 P
    have hB := hx.2 P
    have hθ : (a.2.2.1 P) ∈ (Θ P).H := (Subgroup.mem_pi _).1 a.2.2.2 P (Set.mem_univ _)
    have hC := (q.U_rat P (a.2.2.1 P)).2 hθ
    have hfr : (a • p).fr P = a.1.1 * p.fr P * ((a.2.2.1 P)⁻¹).1 := rfl
    have hγ : toGLm E n a.1.1 = (γ : GL (Fin n) E) := by rw [← h1]; exact qdf_toGLm_ratHom γ
    have key : q.at P (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        ((bc (q.phi P) (qGL n ((a • p).fr P)))⁻¹ * q.at P x')⁻¹ * bc (q.phi P) (qGL n (a.2.2.1 P).1) *
          ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x) := by
      rw [hke, qdf_at_mul, qdf_at_mul, qdf_at_inv, qdf_at_rat, hfr]
      simp only [qGL, map_mul, map_inv, Subgroup.coe_inv]
      rw [hγ]
      group
    rw [key]
    exact mul_mem (mul_mem (inv_mem hA) hC) hB
  exact ⟨γ, ⟨k.1, k.2, Subgroup.mem_iInf.2 hkQ⟩, h1, e⟩

theorem qdf_over_exists (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hE : FrExists (n := n) ST SG Q) (x : UAd hc n) :
    ∃ p : DecoF E n ST SG Q, FrOver q x.1 p := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : ∀ P : Q, Sp E n ≃ₗ[E] Sp E n,
      ∀ (P : Q) y, f P y ∈ (decoOf ST SG x.1).1.at P.1 ↔ y ∈ stdAt E n P.1 :=
    ⟨fun P => (hE (decoOf ST SG x.1) P).choose, fun P => (hE (decoOf ST SG x.1) P).choose_spec⟩
  let p0 : DecoF E n ST SG Q := ⟨(decoOf ST SG x.1, f), fun P y => hf P y⟩
  have hk := fun P : Q => hF x p0 rfl P
  choose g hg using fun P : Q => q.U_dense P _ (hk P).1 (hk P).2
  refine ⟨⟨(decoOf ST SG x.1, fun P => f P * (g P).1), fun P y => ?_⟩, rfl, fun P => ?_⟩
  · show f P ((g P).1 y) ∈ _ ↔ _
    rw [hf P]
    exact (g P).2 y
  · show (Formalism.UG.bc (q.phi P) (qGL n (f P * (g P).1)))⁻¹ * q.at P x.1 ∈ q.U P
    rw [show qGL n (f P * (g P).1) = qGL n (f P) * qGL n (g P).1 from map_mul _ _ _, map_mul, _root_.mul_inv_rev,
      mul_assoc]
    exact hg P

end QCls

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.WithTopLevGTop
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def ChIdx.withTop (L : ChIdx X Pr R Q) (m2 : ℕ) (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) Q) : ChIdx X Pr R Q where
  β j := {b : Option (L.β j) // b.isSome = decide (j ≤ m2 + 1)}
  h j b P := match b.1 with
    | some b' => L.h j b' P
    | none => 1
  levG j b := match b.1 with
    | some b' => L.levG j b'
    | none => Λt j
  levQ j b := match b.1 with
    | some b' => L.levQ j b'
    | none => Θt j

variable (L : ChIdx X Pr R Q) (m2 : ℕ) (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) Q)

def ChIdx.top {j : ℕ} (hj : m2 + 1 < j) : (L.withTop m2 Λt Θt).β j := ⟨none, by simp [Nat.not_le.2 hj]⟩

end Top

end Formalism.L2.Col
end
end

