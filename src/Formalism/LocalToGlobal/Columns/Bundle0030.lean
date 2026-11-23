module

public import Formalism.LocalToGlobal.Columns.Bundle0008
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Formalism.LocalToGlobal.Columns.Bundle0029
public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.LocalToGlobal.Columns.WordFin
public import Formalism.LocalToGlobal.Columns.Bundle0015
public import Formalism.LocalToGlobal.Columns.TiedLv
public import Formalism.LocalToGlobal.Columns.RecLevelLocF
public import Formalism.LocalToGlobal.Columns.Bundle0022
public import Formalism.LocalToGlobal.Columns.Bundle0024
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalToGlobal.Columns.Bundle0023
public import Formalism.LocalToGlobal.Columns.Bundle0013
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Formalism.LocalToGlobal.Columns.Bundle0026
public import Formalism.LocalToGlobal.Columns.Bundle0021
public import Formalism.LocalToGlobal.Columns.Bundle0020
public import Formalism.LocalToGlobal.Columns.Bundle0002
public import Formalism.LocalToGlobal.Columns.RecLevelDiv
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Formalism.LocalToGlobal.Columns.Bundle0027
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Formalism.LocalToGlobal.Columns.Bundle0010
public import Formalism.LocalToGlobal.Columns.Record
public import Formalism.LocalToGlobal.Columns.Bundle0025
public import Formalism.LocalToGlobal.Columns.RecLevelLocK
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Formalism.LocalToGlobal.Columns.Bundle0019
public import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
public import Formalism.LocalToGlobal.Columns.RecLevel
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.ColInst
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
public import Formalism.GL3MeanSquares.Bundle0005
public import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle0004
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.LogRatioLowerBoundOfLogVandermondeGap
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.UpperPlaceHolds
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.VandNSuccRight
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0010
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.Columns.XiRef
public import Formalism.LocalToGlobal.Columns.CoefColLemmas

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.ChainOneP
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem oneYbSym {m2 : ℕ} (hc' : cOf R m2 = 1) (hc : cOf R (m2 + 1) = 0) (hs : cst.sharp = true) : OneYbSym Ch sel mu cst m2 :=
  fun P hP x₀ y' h l => psiAt_sym Ch sel mu cst hc' hc hs P hP x₀ y' h l

theorem oneYbSym_of_m {m2 : ℕ} (hm : R.m = m2 + 2) (hs : cst.sharp = true) : OneYbSym Ch sel mu cst m2 :=
  oneYbSym Ch sel mu cst (by unfold cOf; omega) (by unfold cOf; omega) hs

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.DetChrChi
section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.Col

namespace DetChrChi

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem isSDLat_globLat (hc : CMData F E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    IsSDLat E n (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hspan : Submodule.span E (stdLat E n : Set (Sp E n)) = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun E (Fin n)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    simpa using (single_mem_stdLat (E := E) (n := n) i 1)
  have hlat := Formalism.UG.P.csGlob_lattice (F := F) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) hspan x
  have hU := globLat_unimodular hc n hx
  refine ⟨hlat.toIsLattice.fg, hlat.span_eq_top, fun y => ?_⟩
  conv_lhs => rw [← hU]
  rw [mem_dual]
  refine forall₂_congr fun z _ => ?_
  rw [Submodule.mem_one, RingHom.mem_range]
  exact Iff.rfl

end Lat

section Rep

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

end Rep

section Rel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

end Rel

end DetChrChi

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RecChainYUnfPol
section
open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

section Charts

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))


open Classical in
def cplAt (u : Pr.Word) (m2 j : ℕ) (b : L.β j) : Cpl ((chF W sel mu L u j).mem b) where
  Yb := Set (Sp X.E (R.N j))
  actY :=
    { smul := fun g Y => (fun v => g.1.1 v) '' Y
      one_smul := fun Y => Set.image_id Y
      mul_smul := fun g h Y => (Set.image_image (fun v => g.1.1 v) (fun v => h.1.1 v) Y).symm }
  ys p := if j = m2 + 1 then ybSet sel mu cst p.deco.1.N else {Set.univ}
  fin p := by
    split_ifs
    · exact ybSet_finite sel mu cst _ p.deco.2.lat.fg
    · exact Set.finite_singleton _
  equiv g p Y := by
    split_ifs
    · exact ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y
    · show (fun v => g.1.1 v) '' Y = Set.univ ↔ Y = Set.univ
      constructor
      · intro h
        have h2 : (fun v => g.1.1 v) '' Y = (fun v => g.1.1 v) '' Set.univ := by
          rw [h, Set.image_univ]
          exact (g.1.1.surjective.range_eq).symm
        exact g.1.1.injective.image_injective h2
      · rintro rfl
        rw [Set.image_univ]
        exact g.1.1.surjective.range_eq

@[reducible] def chFY (u : Pr.Word) (m2 j : ℕ) : GFam X.K where
  β := L.β j
  V := (colValF W sel mu u j).V
  ιV := VVIdx (colValF W sel mu u j).lam
  bV := (colValF W sel mu u j).bV
  pair := (colValF W sel mu u j).pair
  G b := FrmG (L.levG j b) (L.levQ j b)
  D b := (cplAt W sel mu cst L u m2 j b).Pts
  actD b := (cplGSD (cplAt W sel mu cst L u m2 j b)).actD
  ρ b := frmRho (colValF W sel mu u j) (L.levG j b) (L.levQ j b)
  Nab _ p := (colValF W sel mu u j).Nab p.1.1
  Del _ p := (colValF W sel mu u j).Del p.1.1

variable {W sel mu cst L}

variable {Ch}

end Charts

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RefXi1Above
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Ref1

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (al : ∀ j, j ≤ m2 + 1 → L.β j) (Am : Amb X) (u : Pr.Word)

def refXi1 : XiFam Pr R u := fun i p p' x => XiRef Ch sel mu cst L m2 al i (liftQ hQ p) (liftQ hQ p') x

end Ref1

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQBridge
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV

section Bridge

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q)
  (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ)

def qbPi (P : Q) : 𝓞 E := Classical.choose (qsp_exists hc P.1 (hQ P))

theorem qbPi_spec (P : Q) : qbPi hc hQ P ∈ P.1.asIdeal ∧ cO E (qbPi hc hQ P) ∉ P.1.asIdeal ∧
    Nonempty (Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P.1) ((qbPi hc hQ P : 𝓞 E) : E)) :=
  Classical.choose_spec (qsp_exists hc P.1 (hQ P))

def qbSp (P : Q) : Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P.1) ((qbPi hc hQ P : 𝓞 E) : E) :=
  Classical.choice (qbPi_spec hc hQ P).2.2

def qbN (P : Q) : ℕ := Classical.choose (hΘ P)

theorem qbN_spec (P : Q) : 0 < qbN Θ hΘ P ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 (qbN Θ hΘ P) (g : Sp E n ≃ₗ[E] Sp E n) →
    ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1 :=
  Classical.choose_spec (hΘ P)

abbrev qbD (P : Q) : E := ((qbPi hc hQ P : 𝓞 E) : E) ^ qbN Θ hΘ P

theorem qbPi_ne (P : Q) : qbPi hc hQ P ≠ 0 := fun h => (qbPi_spec hc hQ P).2.1 (by rw [h, map_zero]; exact zero_mem _)

theorem qbD_ne (P : Q) : qbD hc Θ hQ hΘ P ≠ 0 :=
  pow_ne_zero _ (fun h => qbPi_ne hc hQ P (by exact_mod_cast h))

theorem qbD_val (P : Q) : P.1.valuation E (qbD hc Θ hQ hΘ P) ≤ WithZero.exp (-(qbN Θ hΘ P : ℤ)) := by
  have h1 : qbPi hc hQ P ^ qbN Θ hΘ P ∈ P.1.asIdeal ^ qbN Θ hΘ P := Ideal.pow_mem_pow (qbPi_spec hc hQ P).1 _
  have := (P.1.intValuation_le_pow_iff_mem _ _).2 h1
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)] at this
  simpa using this

abbrev qbF (P : Q) : E →+* (qv F P.1).adicCompletion F := qbPhi hc P.1 (qbPi hc hQ P) (qbSp hc hQ P)

theorem qbF_int (P : Q) (r : 𝓞 E) : Valued.v (qbF hc hQ P (algebraMap (𝓞 E) E r)) ≤ 1 :=
  phi_integral_valuation_le_one hc P.1 _ (qbSp hc hQ P) r

theorem qbF_P (P : Q) (r : 𝓞 E) : Valued.v (qbF hc hQ P (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.1.asIdeal :=
  qsp_sp_P hc P.1 _ (qbPi_spec hc hQ P).1 (qbPi_spec hc hQ P).2.1 (qbSp hc hQ P) r

theorem qbK_mono {v : HeightOneSpectrum (𝓞 F)} {c w : v.adicCompletion F} (hw : w ∈ v.adicCompletionIntegers F)
    {x : GL (Fin n) (v.adicCompletion F)} (hx : x ∈ qbK (c * w)) : x ∈ qbK c := by
  refine ⟨hx.1, hx.2.1, fun i j => ?_⟩
  obtain ⟨z, hz, e⟩ := hx.2.2 i j
  exact ⟨w * z, Subring.mul_mem _ hw hz, by rw [e, mul_assoc]⟩


set_option maxHeartbeats 4000000 in
theorem qbU_dense (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F))
    (hk : qbInt (k : Matrix (Fin n) (Fin n) ((qv F P.1).adicCompletion F)))
    (hk' : qbInt ((k⁻¹ : GL (Fin n) ((qv F P.1).adicCompletion F)) : Matrix (Fin n) (Fin n) ((qv F P.1).adicCompletion F))) :
    ∃ g : ↥(GLint E n P.1), (qbIota P.1 (qbF hc hQ P) g)⁻¹ * k ∈
      qbU P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbF hc hQ P (qbD hc Θ hQ hΘ P)) := by
  obtain ⟨b, hb⟩ := qsp_norm_mem hc (qbPi hc hQ P)
  have hbP : b ∈ (underPl F P.1).asIdeal := by
    show algebraMap (𝓞 F) (𝓞 E) b ∈ P.1.asIdeal
    rw [hb]; exact Ideal.mul_mem_right _ _ (qbPi_spec hc hQ P).1
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, mul_eq_zero] at hb
    rcases hb with h | h
    · exact qbPi_ne hc hQ P h
    · exact (qbPi_spec hc hQ P).2.1 (by rw [h]; exact zero_mem _)
  have hNpos := (qbN_spec Θ hΘ P).1
  have hD0 : b ^ qbN Θ hΘ P ≠ 0 := pow_ne_zero _ hb0
  have hDv : b ^ qbN Θ hΘ P ∈ (underPl F P.1).asIdeal := Ideal.pow_mem_of_mem _ hbP _ hNpos
  obtain ⟨g, hg⟩ := qsp_dense P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (qsp_sp_F hc P.1 _ (qbSp hc hQ P))
    (qsp_isOver P.1) (b ^ qbN Θ hΘ P) hD0 hDv k hk hk'
  have hbE : algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) b =
      qbF hc hQ P ((qbPi hc hQ P : 𝓞 E) : E) * qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F ((qv F P.1).adicCompletion F), ← qsp_sp_F hc P.1 _ (qbSp hc hQ P),
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, hb, map_mul, map_mul]
  have hDE : algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) (b ^ qbN Θ hΘ P) =
      qbF hc hQ P (qbD hc Θ hQ hΘ P) * qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) ^ qbN Θ hΘ P := by
    rw [map_pow, hbE, mul_pow, map_pow]
  rw [hDE] at hg
  have hw : qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) ^ qbN Θ hΘ P ∈ ((qv F P.1).adicCompletionIntegers F) :=
    Subring.pow_mem _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (qbF_int hc hQ P _)) _
  have hg2 := qbK_mono hw hg
  refine ⟨g, hg2.1, hg2.2.1, 1, (Θ P).H.one_mem, ?_⟩
  simpa using hg2

def qbLoc : QLoc hc n Q Θ where
  sp P := (qbSp hc hQ P).φ
  sp_sig P := (qbSp hc hQ P).sig
  sp_alg P := (qbSp hc hQ P).alg
  sp_int P := (qbSp hc hQ P).int
  sp_P P r := qbF_P hc hQ P r
  U P := qbU P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbF hc hQ P (qbD hc Θ hQ hΘ P))
  U_int _ _ hk := hk.1
  U_rat P g := qbU_rat P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbD hc Θ hQ hΘ P) (qbD_ne hc Θ hQ hΘ P)
    (qbD_val hc Θ hQ hΘ P) (qbN_spec Θ hΘ P).2 g
  U_dense P k hk hk' := qbU_dense hc Θ hQ hΘ P k hk hk'
  chr P := qbChr P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbD hc Θ hQ hΘ P) (qbD_ne hc Θ hQ hΘ P)
    (qbD_val hc Θ hQ hΘ P) (qbN_spec Θ hΘ P).2
  chr_rat P g hg h := qbChr_rat P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbD hc Θ hQ hΘ P) (qbD_ne hc Θ hQ hΘ P)
    (qbD_val hc Θ hQ hΘ P) (qbN_spec Θ hΘ P).2 g hg h

end Bridge

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQOrb
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QOrb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

theorem qdf_at_rat (q : QLoc hc n Q Θ) (P : Q) (γ : GL (Fin n) E) : q.at P (bc (iA F E) γ) = bc (q.phi P) γ := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rfl

theorem qdf_at_mul (q : QLoc hc n Q Θ) (P : Q) (x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : q.at P (x * y) = q.at P x * q.at P y := by
  show bc _ (bc _ (x * y)) = _
  rw [map_mul, map_mul]

theorem qdf_at_inv (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : q.at P x⁻¹ = (q.at P x)⁻¹ := by
  show bc _ (bc _ x⁻¹) = _
  rw [map_inv, map_inv]

theorem qdf_levUQ_le (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (q : QLoc hc n Q Θ) : levUQ hc n ST SG Q H q ≤ levU hc n ST SG H := inf_le_left

theorem qdf_levUQ_at (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (q : QLoc hc n Q Θ) {κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : κ ∈ levUQ hc n ST SG Q H q) (P : Q) : q.at P κ ∈ q.U P :=
  (Subgroup.mem_iInf.1 h.2) P

theorem qdf_ratio_val (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n) (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    (qdRatio p p' γ hN P).1 = (p'.fr P)⁻¹ * γ * p.fr P := rfl

variable (H : Subgroup (GLG (E := E) (n := n) (SG := SG)))

theorem qdf_orbit_of_rel (q : QLoc hc n Q Θ) {x x' : UAd hc n} {p p' : DecoF E n ST SG Q}
    (hx : FrOver q x.1 p) (hx' : FrOver q x'.1 p') (γ : URat hc n) (κ : levUQ hc n ST SG Q H q)
    (e : (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
      (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) :
    ∃ a : UF E n × H × Θ.grp, a.1 = ratHom hc n γ ∧ a.2.1 = levRed hc n ST SG H ⟨_, qdf_levUQ_le H q κ.2⟩ ∧ p' = a • p := by
  have hκ : (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ levU hc n ST SG H := qdf_levUQ_le H q κ.2
  have hd : decoOf ST SG (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((ratHom hc n γ, levRed hc n ST SG H ⟨_, hκ⟩) : UF E n × H) • decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [e]; exact rlc_decoOf_sm hc n ST SG H γ ⟨_, hκ⟩ x
  rw [hx.1, hx'.1] at hd
  have hN : p'.deco.1.N = gmap (ratHom hc n γ).1 p.deco.1.N := by rw [hd]; rfl
  have hinj : ∀ a b : GL (Fin n) E, Formalism.UG.glEquiv a = Formalism.UG.glEquiv b → a = b := fun a b h =>
    Units.ext (Matrix.ext_of_mulVec_single fun j => by
      have := congrArg (fun g : Sp E n ≃ₗ[E] Sp E n => g (Pi.single j 1)) h
      simpa [Formalism.UG.glEquiv] using this)
  have hγ : toGLm E n (ratHom hc n γ).1 = (γ : GL (Fin n) E) :=
    hinj _ _ (by rw [glEquiv_toGLm]; rfl)
  have hθ : ∀ P : Q, qdRatio p p' (ratHom hc n γ).1 hN P ∈ (Θ P).H := by
    intro P
    rw [← q.U_rat P]
    have h1 := hx.2 P
    have h2 := hx'.2 P
    have h3 := qdf_levUQ_at H q κ.2 P
    have hx'P : q.at P (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        bc (q.phi P) (γ : GL (Fin n) E) * q.at P x * (q.at P κ)⁻¹ := by
      rw [e, qdf_at_mul, qdf_at_mul, qdf_at_inv, qdf_at_rat]
    have key : bc (q.phi P) (qGL n (qdRatio p p' (ratHom hc n γ).1 hN P).1) =
        ((bc (q.phi P) (qGL n (p'.fr P)))⁻¹ * q.at P x') * q.at P κ * ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x)⁻¹ := by
      rw [qdf_ratio_val]
      simp only [qGL, map_mul, map_inv]
      rw [hγ, hx'P]
      group
    rw [key]
    exact mul_mem (mul_mem h2 h3) (inv_mem h1)
  refine ⟨(ratHom hc n γ, levRed hc n ST SG H ⟨_, hκ⟩, ⟨fun P => qdRatio p p' (ratHom hc n γ).1 hN P,
    (Subgroup.mem_pi _).2 fun P _ => hθ P⟩), rfl, rfl, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hd
  · funext P
    show p'.fr P = (ratHom hc n γ).1 * p.fr P * ((qdRatio p p' (ratHom hc n γ).1 hN P)⁻¹).1
    rw [Subgroup.coe_inv, qdf_ratio_val]
    group

end QOrb

end Formalism.L2.Col
end
end

