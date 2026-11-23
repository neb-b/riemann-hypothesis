module

public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Formalism.LocalToGlobal.Columns.RecLevelDiv
public import Formalism.LocalToGlobal.Columns.Bundle0009
public import Formalism.LocalToGlobal.Columns.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.RecLevelAsm
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn)

section Pack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

structure RecCls (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Lb : Submodule (𝓞 E) (Fin n → E))
    (U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) {cls : Type} (stab : cls → Type) [∀ c, Group (stab c)]
    (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  y : cls → Formalism.UG.UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)
  y_bij : Function.Bijective (fun c : cls =>
    (Quotient.mk'' (y c) : Formalism.UG.ClassSet
      ((Formalism.UG.ratPts hc.sig J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (Formalism.UG.UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)))
      (U.subgroupOf (Formalism.UG.UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)))))
  y_lat : ∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    x ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (lat c) ↔
    ((((y c : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
      Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb
  stabI : ∀ c, stab c →* Formalism.UG.UJ (hc.sig : E →+* E) J
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : GL (Fin n) E) (hγ : γ ∈ Formalism.UG.UJ (hc.sig : E →+* E) J),
    (⟨γ, hγ⟩ : Formalism.UG.UJ (hc.sig : E →+* E) J) ∈ (stabI c).range ↔
      Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈
        U.map (MulAut.conj (y c : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).toMonoidHom
  stabI_lat : ∀ c (γ : stab c) (x : Fin n → E),
    x ∈ lat c ↔ (((stabI c γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) ∈ lat c

end Pack

section Dia

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG (E := E) (n := n) (SG := SG)))

theorem rla_dia_inv (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : (d.dia c⁻¹).dia c = d := by
  apply Subtype.ext
  show (d.1.dia c⁻¹).dia c = d.1
  ext <;> simp [Deco.dia, ← mul_assoc]

theorem rla_dia_inv' (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : (d.dia c).dia c⁻¹ = d := by
  apply Subtype.ext
  show (d.1.dia c).dia c⁻¹ = d.1
  ext <;> simp [Deco.dia, ← mul_assoc]

theorem rla_dia_inj (c : DiaG (E := E) (ST := ST)) {d d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (h : d.dia c = d'.dia c) : d = d' := by
  rw [← rla_dia_inv' n ST SG c d, h, rla_dia_inv' n ST SG c d']

theorem DecoSet.dia_L (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : (d.dia c).1.L = d.1.L := by
  show (d.1.dia c).L = d.1.L
  unfold Deco.L
  congr 1
  ext x
  simp only [Deco.dia, Set.mem_setOf_eq, Units.mul_right_eq_zero]

theorem decoOfD_ptOfD (hS : DecoPtSurj hc n ST SG) (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :
    decoOfD n ST SG c (ptOfD hc n ST SG c d : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d := by
  show (decoOf ST SG (ptOf hc n ST SG (d.dia c⁻¹) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).dia c = d
  rw [decoOf_ptOf hc n ST SG hS (d.dia c⁻¹)]
  exact rla_dia_inv n ST SG c d

theorem rla_dia_smulH (c : DiaG (E := E) (ST := ST)) (g : UF E n × H) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : (g • d).dia c = g • d.dia c := rfl

theorem rla_cls_eq {d d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} :
    decoCls n ST SG H d = decoCls n ST SG H d' ↔ ∃ g : UF E n × H, g • d' = d := by
  constructor
  · intro h
    exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact h))
  · rintro ⟨g, hg⟩
    exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, hg⟩))

theorem levU_y_bijD (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG (E := E) (ST := ST)) (s : DecoCl n ST SG H → DecoSet (E := E) (n := n) (ST := ST) (SG := SG))
    (hs : ∀ c, decoCls n ST SG H (s c) = c) :
    Function.Bijective (fun c : DecoCl n ST SG H =>
      (Quotient.mk'' (ptOfD hc n ST SG c₀ (s c)) : AdCl hc n ST SG H)) := by
  classical

  let Φ : DecoCl n ST SG H → DecoCl n ST SG H := fun q => Quotient.liftOn' q
    (fun d => decoCls n ST SG H (d.dia c₀⁻¹)) (fun a b hab => by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
      rw [← hg]
      exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩)))
  let Ψ : DecoCl n ST SG H → DecoCl n ST SG H := fun q => Quotient.liftOn' q
    (fun d => decoCls n ST SG H (d.dia c₀)) (fun a b hab => by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
      rw [← hg]
      exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩)))
  have hΦΨ : ∀ q, Φ (Ψ q) = q := by
    intro q
    induction q using Quotient.inductionOn' with
    | h d =>
      show decoCls n ST SG H ((d.dia c₀).dia c₀⁻¹) = _
      rw [rla_dia_inv' n ST SG c₀ d]
      rfl
  have hΨΦ : ∀ q, Ψ (Φ q) = q := by
    intro q
    induction q using Quotient.inductionOn' with
    | h d =>
      show decoCls n ST SG H ((d.dia c₀⁻¹).dia c₀) = _
      rw [rla_dia_inv n ST SG c₀ d]
      rfl
  have hΦ : Function.Bijective Φ := Function.bijective_iff_has_inverse.mpr ⟨Ψ, hΨΦ, hΦΨ⟩
  let s' : DecoCl n ST SG H → DecoSet (E := E) (n := n) (ST := ST) (SG := SG) := fun c => (s (Ψ c)).dia c₀⁻¹
  have hs' : ∀ c, decoCls n ST SG H (s' c) = c := by
    intro c
    calc decoCls n ST SG H (s' c) = Φ (decoCls n ST SG H (s (Ψ c))) := rfl
      _ = Φ (Ψ c) := by rw [hs (Ψ c)]
      _ = c := hΦΨ c
  have hF := levU_y_bij hc n ST SG H hS s' hs'
  have heq : (fun c : DecoCl n ST SG H => (Quotient.mk'' (ptOfD hc n ST SG c₀ (s c)) : AdCl hc n ST SG H)) =
      (fun c => (Quotient.mk'' (ptOf hc n ST SG (s' (Φ c))) : AdCl hc n ST SG H)) := by
    funext c
    show _ = (Quotient.mk'' (ptOf hc n ST SG ((s (Ψ (Φ c))).dia c₀⁻¹)) : AdCl hc n ST SG H)
    rw [hΨΦ c]
    rfl
  rw [heq]
  exact hF.comp hΦ

theorem rla_mem_stab_dia (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (g : UF E n × H) :
    g ∈ MulAction.stabilizer (UF E n × H) (d.dia c) ↔ g ∈ MulAction.stabilizer (UF E n × H) d := by
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact rla_dia_inj n ST SG c (d := g • d) (d' := d) h
  · intro h
    show (g • d).dia c = d.dia c
    rw [h]

theorem rla_mem_range_stabRat (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (γ : URat hc n) :
    γ ∈ (stabRat hc n ST SG H d).range ↔ ∃ h : H, (ratHom hc n γ, h) ∈ MulAction.stabilizer (UF E n × H) d := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a.1.2, ?_⟩
    rw [rlc_ratHom_stabRat hc n ST SG H d a]
    exact a.2
  · rintro ⟨h, hmem⟩
    refine ⟨⟨(ratHom hc n γ, h), hmem⟩, ?_⟩
    apply (ratHom_bijective hc n).1
    rw [rlc_ratHom_stabRat]

theorem stabRat_rangeD (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (y : UAd hc n)
    (hy : decoOfD n ST SG c (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d) (γ : URat hc n) :
    γ ∈ (stabRat hc n ST SG H d).range ↔
      Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) ∈
        (levU hc n ST SG H).map (MulAut.conj (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).toMonoidHom := by
  have hy' : decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d.dia c⁻¹ := by
    rw [← hy]
    exact (rla_dia_inv' n ST SG c _).symm
  rw [← stabRat_range hc n ST SG H (d.dia c⁻¹) y hy' γ, rla_mem_range_stabRat, rla_mem_range_stabRat]
  simp only [rla_mem_stab_dia]

theorem levU_y_latD (hS : DecoPtSurj hc n ST SG) (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG))
    (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    x ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) d.1.L ↔
    ((((ptOfD hc n ST SG c d : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
      Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (baseLb E n ST) := by
  rw [← DecoSet.dia_L n ST SG c⁻¹ d]
  exact levU_y_lat hc n ST SG hS (d.dia c⁻¹) x

def recCls (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG (E := E) (ST := ST)) (s : DecoCl n ST SG H → DecoSet (E := E) (n := n) (ST := ST) (SG := SG))
    (hs : ∀ c, decoCls n ST SG H (s c) = c) :
    RecCls hc (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST) (levU hc n ST SG H)
      (fun c => MulAction.stabilizer (UF E n × H) (s c)) (fun c => (s c).1.L) where
  y c := ptOfD hc n ST SG c₀ (s c)
  y_bij := levU_y_bijD hc n ST SG H hS c₀ s hs
  y_lat c x := levU_y_latD hc n ST SG hS c₀ (s c) x
  stabI c := stabRat hc n ST SG H (s c)
  stabI_inj c := stabRat_injective hc n ST SG H (s c)
  stabI_range c γ hγ := stabRat_rangeD hc n ST SG H c₀ (s c) _ (decoOfD_ptOfD hc n ST SG hS c₀ (s c)) ⟨γ, hγ⟩
  stabI_lat c γ x := stabRat_lat hc n ST SG H (s c) γ x

end Dia

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RecLevelSym
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn)

section ColsSym

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem r_le_N_of_le {j : ℕ} (hj : R.m ≤ j + 1) : R.r ≤ R.N j := by
  have h1 := N_eq_blocks R j
  have h2 := Ranks.r_eq (R := R)
  rw [h1]
  generalize j * R.t = z at *
  omega

theorem colK_le_N (R : Ranks) (j : ℕ) : R.k ≤ R.N j := by
  rw [N_eq_blocks]
  exact le_add_right (Nat.le_add_right _ _)

theorem Y_eq_X_add {j : ℕ} (hj : j + 1 ≤ R.m) : R.r + j * R.t = R.N j + (R.m - 1 - j) := by
  have h1 := N_eq_blocks R j
  have h2 := Ranks.r_eq (R := R)
  rw [h1]
  generalize j * R.t = z at *
  omega

theorem r_le_Y {j : ℕ} (hj : j + 1 ≤ R.m) : R.r ≤ R.N j + (R.m - 1 - j) := by
  rw [← Y_eq_X_add hj]
  exact Nat.le_add_right _ _

def colLevSym (Ch : Chars X Pr R.m) (j : ℕ) : LevFam X.E X.K (R.N j) Pr.vGs := fun w =>
  if j = 0 then colLev Ch j w
  else if h1 : j + 1 < R.m then
    ⟨(HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))).comap
        (insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl),
      (lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))).comp
        ((insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl).subgroupComap _)⟩
  else if hj : j + 1 = R.m then
    ⟨HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t j R.rS (r_le_N_of_le hj.ge),
      lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t j R.rS (r_le_N_of_le hj.ge)⟩
  else
    ⟨HXmsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega)),
      lamXmsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega))⟩

variable (hc : Formalism.BasicNotions.CMData X.F X.E) (Ch : Chars X Pr R.m)

end ColsSym

section SymTies

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (hc : Formalism.BasicNotions.CMData X.F X.E) (Ch : Chars X Pr R.m)

theorem colLevSym_pred {j : ℕ} (hj : j + 1 = R.m) :
    colLevSym Ch j = parFam (r_le_N_of_le hj.ge) R.t j (rPsymF Ch) (fun w => extChi fun s => Ch.chi s w) := by
  funext w
  unfold colLevSym
  rw [if_neg (by have := R.two_le_m; omega), dite_eq_right (by omega), dite_eq_left hj]
  rfl

theorem colLevSym_top_H {j : ℕ} (hj : R.m ≤ j) (w : Pr.vGs) :
    (colLevSym Ch j w).H = HXmsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega)) := by
  have h2 := R.two_le_m
  unfold colLevSym
  rw [if_neg (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]

theorem colLevSym_top_lam {j : ℕ} (hj : R.m ≤ j) (w : Pr.vGs) (M : ↥(colLevSym Ch j w).H)
    (hM : M.1 ∈ HXmsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega))) :
    (colLevSym Ch j w).lam M =
      lamXmsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega)) ⟨M.1, hM⟩ := by
  have key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N j), l = colLevSym Ch j w → ∀ (M' : ↥l.H) (hM' : M'.1 ∈ HXmsym
      (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega))),
      l.lam M' = lamXmsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega)) ⟨M'.1, hM'⟩ := by
    intro l hl M' hM'
    have hl' : l = ⟨HXmsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega)),
        lamXmsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega))⟩ := by
      rw [hl]; unfold colLevSym; rw [if_neg (by have := R.two_le_m; omega), dite_eq_right (by omega), dite_eq_right (by omega)]
    subst hl'
    rfl
  exact key _ rfl M hM

theorem N_pred_eq {j : ℕ} (hj : j + 1 = R.m) : R.N j = R.r + j * R.t := by
  have h := Y_eq_X_add (R := R) (j := j) (by omega)
  rw [show R.m - 1 - j = 0 by omega, add_zero] at h
  exact h.symm

theorem colLevSym_zero : colLevSym Ch 0 = colLev Ch 0 := by
  funext w
  simp [colLevSym]

theorem colLevSym_mid_H {j : ℕ} (h0 : j ≠ 0) (h1 : j + 1 < R.m) (w : Pr.vGs) :
    (colLevSym Ch j w).H = (HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))).comap
      (insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl) := by
  unfold colLevSym
  rw [if_neg h0, dite_eq_left h1]

theorem colLevSym_mid_lam {j : ℕ} (h0 : j ≠ 0) (h1 : j + 1 < R.m) (w : Pr.vGs) (M : ↥(colLevSym Ch j w).H)
    (hM : insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl M.1 ∈
      HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))) :
    (colLevSym Ch j w).lam M = lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS
      (r_le_Y (by omega)) ⟨_, hM⟩ := by
  have key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N j), l = colLevSym Ch j w → ∀ (M' : ↥l.H) (hM' : insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j)
      (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl M'.1 ∈
      HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))),
      l.lam M' = lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega)) ⟨_, hM'⟩ := by
    intro l hl M' hM'
    have hl' : l = ⟨(HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))).comap
          (insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl),
        (lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))).comp
          ((insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl).subgroupComap _)⟩ := by
      rw [hl]; unfold colLevSym; rw [if_neg h0, dite_eq_left h1]
    subst hl'
    rfl
  exact key _ rfl M hM

end SymTies

section SymDivTies

variable {κ : Type} [CommRing κ] {K : Type} [Field K]

theorem HPsym_eq_unipSym (r k rS : ℕ) : HPsym κ r k rS = Formalism.L2.DIV.unipSym κ r rS k := by
  ext M
  show ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ _)
  have e1 : (M : Matrix (Fin r) (Fin r) κ).BlockTriangular (fun i => fine r [] i.val) ↔
      (M : Matrix (Fin r) (Fin r) κ).BlockTriangular (fun i => i.val) := by
    have : (fun i : Fin r => fine r [] i.val) = (fun i => i.val) := funext fun i => fine_self_lt i.2
    rw [this]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨e1.mp h1, fun i => h2 i i.2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨e1.mpr h1, fun i _ => h2 i⟩, h3⟩

theorem HPsymF_eq_comap_unipSym (r k rS : ℕ) :
    HPsymF κ r k rS = (Formalism.L2.DIV.unipSym κ r rS k).comap (toSymOrd κ r k rS) := by
  rw [HPsymF, HPsym_eq_unipSym]

theorem sym_sum_split {r k rS : ℕ} (M : GL (Fin r) κ) :
    supSum r (SPsym r k rS) (M : Matrix (Fin r) (Fin r) κ) + offSum k rS (M : Matrix (Fin r) (Fin r) κ) =
      Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge rS k) M := by
  unfold supSum offSum Formalism.L2.DIV.edgeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := j.2
  rcases Decidable.em (Formalism.L2.DIV.symEdge rS k i j) with hE | hE
  · rw [if_pos hE]
    unfold Formalism.L2.DIV.symEdge at hE
    simp only [SPsym, Finset.mem_filter, Finset.mem_range]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [if_neg hE]
    unfold Formalism.L2.DIV.symEdge at hE
    simp only [SPsym, Finset.mem_filter, Finset.mem_range]
    split_ifs <;> first | (exfalso; omega) | simp

theorem chiSym_eq_symHom (ψ : AddChar κ K) (r k rS : ℕ) (M : ↥(HPsym κ r k rS)) (hM : M.1 ∈ Formalism.L2.DIV.unipSym κ r rS k) :
    ((chiSym ψ r k rS M : Kˣ) : K) = ((Formalism.L2.DIV.addCharHom ψ (Formalism.L2.DIV.symHom κ r rS k) ⟨M.1, hM⟩ : Kˣ) : K) := by
  show ψ (supSum r (SPsym r k rS) (M.1 : Matrix (Fin r) (Fin r) κ)) * ψ (offSum k rS (M.1 : Matrix (Fin r) (Fin r) κ)) =
    ψ (Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge rS k) M.1)
  rw [← AddChar.map_add_eq_mul, sym_sum_split]

def SPsymF (n k : ℕ) : Finset ℕ := (Finset.range (n - 1)).filter fun i => i + 1 ≠ k

theorem symEdge_symPerm_iff {n k rS : ℕ} (hn : n = k + 2 * rS + 1) (i j : Fin n) :
    Formalism.L2.DIV.symEdge rS k (symPerm n k rS i) (symPerm n k rS j) ↔
      (i.val + 1 = j.val ∧ j.val < n ∧ i.val ∈ SPsymF n k) := by
  have h : k + rS ≤ n := by omega
  unfold Formalism.L2.DIV.symEdge
  rw [symPerm_val h, symPerm_val h]
  simp only [SPsymF, Finset.mem_filter, Finset.mem_range]
  have hi := i.2
  have hj := j.2
  unfold symIdx
  split_ifs <;> omega

theorem chiSymF_val {n k rS : ℕ} (hn : n = k + 2 * rS + 1) (ψ : AddChar κ K) (M : ↥(HPsymF κ n k rS)) :
    ((chiSymF ψ n k rS M : Kˣ) : K) = ψ (supSum n (SPsymF n k) (M.1 : Matrix (Fin n) (Fin n) κ)) := by
  have hM : toSymOrd κ n k rS M.1 ∈ Formalism.L2.DIV.unipSym κ n rS k := by
    have := M.2
    rw [mem_HPsymF, HPsym_eq_unipSym] at this
    exact this
  rw [chiSymF_apply, chiSym_eq_symHom ψ n k rS _ hM]
  show ψ (Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge rS k) (toSymOrd κ n k rS M.1)) = _
  congr 1
  unfold Formalism.L2.DIV.edgeSum supSum
  rw [← Equiv.sum_comp (symPerm n k rS)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (symPerm n k rS)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toSymOrd_val']
  by_cases hE : Formalism.L2.DIV.symEdge rS k (symPerm n k rS i) (symPerm n k rS j)
  · rw [if_pos hE, if_pos ((symEdge_symPerm_iff hn i j).mp hE)]
  · rw [if_neg hE, if_neg (fun h => hE ((symEdge_symPerm_iff hn i j).mpr h))]

end SymDivTies

section SymRanks

open Formalism.BasicNotions (Ranks)

theorem r_eq_sym (R : Ranks) : R.r = R.k + 2 * R.rS + 1 := by
  have h1 := Ranks.r_eq (R := R)
  have h2 := Ranks.rS_two (R := R)
  omega

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

end SymRanks

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedTilA
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

section Pad

variable {R : Type} [CommRing R] {n : ℕ}

end Pad

section Ad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem til_tmv_int_of_iA {a : E} (h : iA F E a ∈ Formalism.L2.Herm.intAf F E) : ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = a := by
  have h1 : (fun _ : Fin 1 => a) ∈ Formalism.UG.CS.globLat (F := F) (1 : GL (Fin 1) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E 1) := by
    rw [mem_globLat]
    intro i
    rw [pullV_one]
    exact h
  rw [globLat_one_std, mem_stdLat] at h1
  exact h1 0

private lemma mk_mul_reduction_eq_mk (P : HeightOneSpectrum (𝓞 E)) {x : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E r) :
    Ideal.Quotient.mk P.asIdeal s * redP P x = Ideal.Quotient.mk P.asIdeal r := by
  classical
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, h, by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs0, mul_one]⟩
  unfold redP
  rw [dite_eq_left hex]
  obtain ⟨r', s', hs', h', hc'⟩ := hex.choose_spec
  have hs'0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have key : s * r' = s' * r := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, map_mul, ← h', ← h]
    ring
  apply mul_left_cancel₀ hs'0
  rw [mul_left_comm, hc', ← map_mul, ← map_mul, key]

variable {n : ℕ} [NeZero n] (ST SG : Finset (Pl E))

private lemma reduction_mul_of_integral' (P : Pl E) (b : 𝓞 E) {a : E} (ha : IntAt P a) :
    redP P (algebraMap (𝓞 E) E b * a) = Ideal.Quotient.mk P.asIdeal b * redP P a := by
  obtain ⟨r, s, hs, h⟩ := ha
  haveI : P.asIdeal.IsPrime := P.isPrime
  have h1 := mk_mul_reduction_eq_mk P hs h
  have h2 := mk_mul_reduction_eq_mk P (x := algebraMap (𝓞 E) E b * a) (r := b * r) hs (by rw [map_mul, ← h]; ring)
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  apply mul_left_cancel₀ hs0
  rw [h2, mul_left_comm, h1, map_mul]

end Ad

end Formalism.L2.Col
end
end

