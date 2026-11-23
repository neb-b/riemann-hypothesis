module

public import Formalism.LocalToGlobal.Columns.Bundle0034
public import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.Bundle0008
public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ColInst
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Formalism.LocalToGlobal.Columns.Bundle0010
public import Formalism.LocalToGlobal.Columns.Bundle0031
public import Formalism.LocalToGlobal.Columns.Bundle0035

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.ChainLawXi
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Units

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {K : Type} [Field K]

theorem clX_unitV_ne (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (hU : IsUnit (redP P a)) : LocE.unitV χ a ≠ 0 := by
  unfold LocE.unitV
  rw [dite_eq_left hU]
  exact Units.ne_zero _

theorem clX_unitV_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.unitV χ (1 : E) = 1 := by
  have h1 : redP P (1 : E) = 1 := by
    have := reduction_coe P (1 : 𝓞 E)
    simpa using this
  have hU : IsUnit (redP P (1 : E)) := by rw [h1]; exact isUnit_one
  unfold LocE.unitV
  rw [dite_eq_left hU]
  have : hU.unit = 1 := Units.ext (by simpa using h1)
  rw [this, map_one, Units.val_one]

theorem clX_unitV_inv (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (hu : IntAt P a) (hu' : IntAt P a⁻¹) (h0 : a ≠ 0) :
    LocE.unitV χ a⁻¹ = (LocE.unitV χ a)⁻¹ := by
  have hne := clX_unitV_ne χ (isUnit_reduction_of_integralAt_inv hu hu' h0)
  have hm := unitV_mul_unit χ hu hu' h0 a⁻¹
  rw [inv_mul_cancel₀ h0, clX_unitV_one] at hm
  exact eq_inv_of_mul_eq_one_left hm.symm

end Units

section Assembly

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

end Assembly

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.StabilizerMapTopIndexAlt
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc.Fr

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Col Formalism.L2.Col.Sc

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (cst : LocCst X (rowSG Pr sel mu)) (L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

attribute [local instance] ptYAct


variable (sel mu) in
structure TopFr where
  fr : ∀ (_P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (_d : DecoSet (E := X.E) (n := R.N R.m - 1) (ST := ∅) (SG := SG')), Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)
  spec : ∀ P d x, fr P d x ∈ localization₂ P.1.asIdeal (tilR hSG u d).1.N ↔ x ∈ stdAt X.E (R.N R.m) P.1

variable (hm : R.m = m2 + 2) (F : TopFr sel mu u hSG)

variable {W cst L₀ u m2 Λt Θt hSG ΛM hm F}

variable (sec : SecY W sel mu cst (L₀.withTop m2 Λt Θt) u m2)

end Top

end Formalism.L2.Col.Sc.Fr
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQExact
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QExact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

def FrExact (q : QLoc hc n Q Θ) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (p : DecoF E n ST SG Q) : Prop :=
  decoOf ST SG x = p.deco ∧ ∀ P : Q, q.at P x = bc (q.phi P) (qGL n (p.fr P))

theorem FrExact.over {q : QLoc hc n Q Θ} {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {p : DecoF E n ST SG Q} (h : FrExact q x p) :
    FrOver q x p := by
  refine ⟨h.1, fun P => ?_⟩
  rw [h.2 P, inv_mul_cancel]
  exact (q.U P).one_mem

variable {H : Subgroup (GLG (E := E) (n := n) (SG := SG))}

def recClsFy (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hE : FrExists (n := n) ST SG Q)
    (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q) (hs : ∀ c, (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q H Θ) = c)
    (y : DecoFCl (K := K) n ST SG Q H Θ → UAd hc n) (hy : ∀ c, FrOver q (y c).1 (s c)) :
    RecClsF hc n ST SG Q H q s where
  y c := y c
  y_bij := by
    constructor
    · intro c c' h
      have hr := Quotient.exact' h
      obtain ⟨h0, hh, k, hk, e⟩ := DoubleCoset.rel_iff.1 hr
      obtain ⟨γ, hγ⟩ := Formalism.L2.DIV.ratEl_surjective (⟨h0, hh⟩ : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E))
      have hh' : ((h0 : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) :=
        (congrArg (fun z : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E) =>
          ((z : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) hγ).symm
      have hk' : ((k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ ∈ levUQ hc n ST SG Q H q :=
        Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hk)
      have e' : ((y c' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
          Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            (((⟨_, hk'⟩ : levUQ hc n ST SG Q H q) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))⁻¹ := by
        have e2 := congrArg (fun z : UAd hc n => (z : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) e
        simp only [Subgroup.coe_mul] at e2
        rw [e2, hh', inv_inv]
      obtain ⟨a, -, -, ha⟩ := qdf_orbit_of_rel H q (hy c) (hy c') γ ⟨_, hk'⟩ e'
      rw [← hs c, ← hs c']
      exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨a⁻¹, by show a⁻¹ • s c' = s c; rw [ha, inv_smul_smul]⟩)
    · intro Qc
      induction Qc using Quotient.inductionOn' with
      | h x =>
        obtain ⟨p, hp⟩ := qdf_over_exists q hF hE x
        refine ⟨Quotient.mk'' p, ?_⟩
        obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.1 (Quotient.exact (hs (Quotient.mk'' p)))
        have ha' : a • p = s (Quotient.mk'' p) := ha
        have hx' : FrOver q (y (Quotient.mk'' p)).1 (a • p) := by
          rw [ha']; exact hy _
        obtain ⟨γ, κ, -, e⟩ := qdf_rel_of_orbit H q a hp hx'
        exact (qdf_mk_eq H q γ κ e).symm
  y_lat c x := by
    have h := decoRaw_carries hc n ST SG (y c).2 x
    rw [← rlc_decoOf_val hc n ST SG (y c).2, (hy c).1] at h
    exact h
  stabI c := qdStab H (s c)
  stabI_inj c := by
    intro a b hab
    have h1 : a.1.1 = b.1.1 := by rw [← qdf_ratHom_stab (hc := hc) H (s c) a, ← qdf_ratHom_stab (hc := hc) H (s c) b, hab]
    have ha := qdf_stab_deco H (s c) a
    have hb := qdf_stab_deco H (s c) b
    have hab' : ((a.1.1, (a.1.2.1 : GLG (E := E) (n := n) (SG := SG))) : UF E n × GLG (E := E) (n := n) (SG := SG)) • (s c).deco = (s c).deco := ha
    have hbb' : ((b.1.1, (b.1.2.1 : GLG (E := E) (n := n) (SG := SG))) : UF E n × GLG (E := E) (n := n) (SG := SG)) • (s c).deco = (s c).deco := hb
    have h2 := DecoSet.stab_fst_injective (s c).deco hab' hbb' h1
    have h3 : a.1.2.2 = b.1.2.2 := by
      apply Subtype.ext
      funext P
      apply Subtype.ext
      rw [qdf_stab_fr H (s c) a P, qdf_stab_fr H (s c) b P, h1]
    exact Subtype.ext (Prod.ext h1 (Prod.ext (Subtype.ext (congrArg Prod.snd h2)) h3))
  stabI_range c γ hγ := by
    constructor
    · rintro ⟨a, ha⟩
      have hx := hy c
      have hx' : FrOver q (y c).1 (a.1 • s c) := by rw [a.2]; exact hx
      obtain ⟨γ', κ, h1, e⟩ := qdf_rel_of_orbit H q a.1 hx hx'
      have hγ' : γ' = ⟨γ, hγ⟩ := by
        rw [← ha]
        exact (ratHom_bijective hc n).1 (h1.trans (qdf_ratHom_stab (hc := hc) H (s c) a).symm)
      refine ⟨κ.1, κ.2, ?_⟩
      show ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * κ.1 *
        ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ = _
      have e' : Formalism.UG.bc (iA F E) (γ' : GL (Fin n) E) = ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          κ.1 * ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ :=
        eq_mul_inv_of_mul_eq (eq_mul_inv_iff_mul_eq.1 e).symm
      rw [← e', hγ']
    · rintro ⟨k, hk, e⟩
      have e' : ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * k *
          ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ =
          Formalism.UG.bc (iA F E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) E) := e
      have e2 : ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
          Formalism.UG.bc (iA F E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) E) *
            ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            ((⟨k, hk⟩ : levUQ hc n ST SG Q H q) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
        rw [← e']; group
      obtain ⟨a, ha1, -, ha⟩ := qdf_orbit_of_rel H q (hy c) (hy c) ⟨γ, hγ⟩ ⟨k, hk⟩ e2
      refine ⟨⟨a, ha.symm⟩, ?_⟩
      apply (ratHom_bijective hc n).1
      rw [qdf_ratHom_stab (hc := hc) H (s c) ⟨a, ha.symm⟩, ha1]
  stabI_lat c a x := by
    have h := stabRat_lat hc n ST SG H (s c).deco ⟨_, qdf_stab_deco H (s c) a⟩ x
    have e : stabRat hc n ST SG H (s c).deco ⟨_, qdf_stab_deco H (s c) a⟩ = qdStab H (s c) a :=
      (ratHom_bijective hc n).1 ((rlc_ratHom_stabRat hc n ST SG H _ _).trans (qdf_ratHom_stab (hc := hc) H (s c) a).symm)
    rw [e] at h
    exact h

end QExact

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.XtSumSingle
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Std

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem xt_sum_single {a b : ℕ} (z : HomE E a b) (v : Sp E a) : z v = ∑ j, v j • z (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (v j) : Sp E a) = v j • Pi.single j 1 := by rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul]

theorem xt_map_std {a b : ℕ} (z : HomE E a b) (hz : ∀ j l, IntAt P (z (Pi.single j 1) l)) {v : Sp E a} (hv : v ∈ stdAt E a P) :
    z v ∈ stdAt E b P := by
  rw [ciMem_stdAt] at hv ⊢
  intro l
  rw [xt_sum_single z v, Finset.sum_apply]
  exact ciIntAt_sum _ _ fun j _ => by
    rw [Pi.smul_apply, smul_eq_mul]
    exact (hv j).mul (hz j l)

end Std

section Law

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def TopLawG (m2 : ℕ) (Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs) (b : L.β (m2 + 1)) : Prop :=
  ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) (h : ↥(L.levG (m2 + 1) b ⟨w.1, hw⟩).H) (h' : ↥(Λm ⟨w.1, hw⟩).H)
    (κ : ↥(GLint X.E (R.N (m2 + 1)) w.1)) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1)),
    (∀ x ∈ stdAt X.E (R.N (m2 + 1)) w.1, redV w.1 (κ.1 x) = (h.1⁻¹).1.mulVec (redV w.1 x)) →
    (∀ x ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1, redV w.1 (κ'.1 x) = (h'.1⁻¹).1.mulVec (redV w.1 x)) →
    ∀ y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1)), (∀ j l, IntAt w.1 (y (Pi.single j 1) l)) →
      rhoS Ch sel mu (m2 + 1) w (LinearEquiv.det κ.1 : X.Eˣ) * rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) *
          PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ
            (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
        (((Λm ⟨w.1, hw⟩).lam h' : X.Kˣ) : X.K) * ((((L.levG (m2 + 1) b ⟨w.1, hw⟩).lam h)⁻¹ : X.Kˣ) : X.K) *
          PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ
            LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))

def LastRow {j : ℕ} (Λm : LevFam X.E X.K (R.N j) Pr.vGs) : Prop :=
  ∀ (w : Pr.vGs), ∀ h' ∈ (Λm w).H, ∀ l : Fin (R.N j),
    (h'.1 : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)) ⟨R.N j - 1, xt_last_lt R j⟩ l = if l.1 = R.N j - 1 then 1 else 0

variable {Ch sel mu cst L}

theorem topDat_law (hc : cst.Ok) {m2 : ℕ} (hn : TopNum R (m2 + 1)) {Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs} {b : L.β (m2 + 1)}
    (hLaw : TopLawG Ch sel mu cst L m2 Λm b) (hRow : LastRow Λm)
    (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) (h : ↥(L.levG (m2 + 1) b ⟨w.1, hw⟩).H) (h' : ↥(Λm ⟨w.1, hw⟩).H)
    (κ : ↥(GLint X.E (R.N (m2 + 1)) w.1)) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1))
    (hκ : ∀ x ∈ stdAt X.E (R.N (m2 + 1)) w.1, redV w.1 (κ.1 x) = (h.1⁻¹).1.mulVec (redV w.1 x))
    (hκ' : ∀ x ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1, redV w.1 (κ'.1 x) = (h'.1⁻¹).1.mulVec (redV w.1 x))
    (hu : ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2)
    (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ y₂ : Sp X.E (R.N (m2 + 1))) (hδ : κ.1 y₁ - y₂ ∈ stdAt X.E (R.N (m2 + 1)) w.1)
    (hq : ((qOf w.1 : ℕ) : X.E) • y₂ ∈ stdAt X.E (R.N (m2 + 1)) w.1) :
    rhoS Ch sel mu (m2 + 1) w (LinearEquiv.det κ.1 : X.Eˣ) * rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) *
        topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) y₁ =
      (((Λm ⟨w.1, hw⟩).lam h' : X.Kˣ) : X.K) * ((((L.levG (m2 + 1) b ⟨w.1, hw⟩).lam h)⁻¹ : X.Kˣ) : X.K) *
        topDat Ch sel mu cst (m2 + 1) w y y₂ := by
  have hk : ∀ v, κ.1 v ∈ stdAt X.E (R.N (m2 + 1)) w.1 ↔ v ∈ stdAt X.E (R.N (m2 + 1)) w.1 := κ.2
  have hk' : ∀ v, κ'.1 v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 ↔ v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 := κ'.2
  by_cases hint : ∀ j l, IntAt w.1 (y (Pi.single j 1) l)
  ·
    have hF : ftY sel mu cst w (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap)) y₁ =
        ftY sel mu cst w (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y₂ := by
      have e1 : atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) =
          (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.1.symm.toLinearMap ∘ₗ y) ∘ₗ κ.1.toLinearMap := rfl
      rw [e1, ftY_move2 sel mu cst hc w hw κ _ y₂ y₁ hδ hq]
      set ζ : Sp X.E (R.N (m2 + 1)) →ₗ[X.E] X.E :=
        atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.1.symm.toLinearMap ∘ₗ y - atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y with hζdef
      have e2 : atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.1.symm.toLinearMap ∘ₗ y =
          atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y + ζ := by rw [hζdef]; abel

      have hζq : ∀ i, IntAt w.1 (ζ (Pi.single i 1) / (qOf w.1 : X.E)) := by
        intro i
        set v := y (Pi.single i 1) with hv
        have hvs : v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 := (ciMem_stdAt _ _).2 (hint i)
        have hvs' : κ'.1.symm v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 := (hk' _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hvs)
        have h1 := hκ' _ hvs'
        rw [LinearEquiv.apply_symm_apply] at h1
        have h2 : redV w.1 (κ'.1.symm v) = h'.1.1.mulVec (redV w.1 v) := by
          rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        have h3 : redP w.1 (κ'.1.symm v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩) = redP w.1 (v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩) := by
          have h20 := congrFun h2 ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩
          have e : (h'.1.1.mulVec (redV w.1 v)) ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ = redV w.1 v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ := by
            show ∑ l, h'.1.1 ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ l * redV w.1 v l = _
            rw [Finset.sum_eq_single (⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ : Fin (R.N (m2 + 1 + 1)))]
            · rw [hRow ⟨w.1, hw⟩ h'.1 h'.2 ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩, if_pos rfl, one_mul]
            · intro l _ hl
              rw [hRow ⟨w.1, hw⟩ h'.1 h'.2 l, if_neg (fun hh => hl (Fin.ext hh)), zero_mul]
            · intro hh
              exact absurd (Finset.mem_univ _) hh
          exact h20.trans e
        have ha := (ciMem_stdAt _ _).1 hvs' ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩
        have hb := (ciMem_stdAt _ _).1 hvs ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩
        have e3 : ζ (Pi.single i 1) = κ'.1.symm v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ - v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ := by
          rw [hζdef, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, xt_atNL, xt_atNL]
          rfl
        rw [e3]
        exact ciIntAt_div (ciQ_mem w.1) hu (ciIntAt_sub ha hb) (by rw [redP_sub ha hb, h3, sub_self])
      have hq0 : (qOf w.1 : X.E) ≠ 0 := ciQ_ne_zero hu
      have hζ : ∀ i, IntAt w.1 (ζ (Pi.single i 1)) := fun i => by
        have := (ciIntAt_q (q := qOf w.1)).mul (hζq i)
        rwa [mul_div_cancel₀ _ hq0] at this
      have hζy : IntAt w.1 (ζ y₂) := by
        have e4 : ζ y₂ = ∑ j, y₂ j * ζ (Pi.single j 1) := by
          conv_lhs => rw [← Finset.univ_sum_single y₂]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          have : (Pi.single j (y₂ j) : Sp X.E (R.N (m2 + 1))) = y₂ j • Pi.single j 1 := by rw [← Pi.single_smul, smul_eq_mul, mul_one]
          rw [this, map_smul, smul_eq_mul]
        rw [e4]
        refine ciIntAt_sum _ _ fun j _ => ?_
        have h1 := (ciMem_stdAt _ _).1 hq j
        rw [Pi.smul_apply, smul_eq_mul] at h1
        have h2 := h1.mul (hζq j)
        have e5 : ((qOf w.1 : ℕ) : X.E) * y₂ j * (ζ (Pi.single j 1) / (qOf w.1 : X.E)) = y₂ j * ζ (Pi.single j 1) := by
          field_simp
        rwa [e5] at h2
      rw [e2]
      exact fourierTwist_add_integral sel mu cst hc w hw _ ζ y₂ hζ hζy hq
    unfold topDat
    rw [hF, ← mul_assoc, hLaw w hw h h' κ κ' hκ hκ' y hint, mul_assoc]
  ·
    have r0 : topDat Ch sel mu cst (m2 + 1) w y y₂ = 0 := by
      by_contra hne
      exact hint fun j l => topDat_int Ch sel mu cst hn w hw y y₂ hne j l
    have l0 : topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) y₁ = 0 := by
      by_contra hne
      have hz := fun j l => topDat_int Ch sel mu cst hn w hw _ y₁ hne j l
      refine hint fun j l => ?_
      have h1 : κ.1.symm (Pi.single j 1) ∈ stdAt X.E (R.N (m2 + 1)) w.1 :=
        (hk _).1 (by rw [LinearEquiv.apply_symm_apply]; exact ciSingle_mem j)
      have h2 := xt_map_std _ hz h1
      have h3 : (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) (κ.1.symm (Pi.single j 1)) = κ'.1.symm (y (Pi.single j 1)) := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [h3] at h2
      have h4 := (hk' _).2 h2
      rw [LinearEquiv.apply_symm_apply] at h4
      exact (ciMem_stdAt _ _).1 h4 l
    rw [r0, l0, mul_zero, mul_zero]

end Law

end Formalism.L2.Col
end
end

