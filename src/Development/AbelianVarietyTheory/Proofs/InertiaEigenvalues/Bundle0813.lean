module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0799
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0804
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtSplitPlaceDeterminant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.HeckeDetValue

theorem chr_detAt : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (Q : Finset (Pl D.host.E)) (V : HSp D) (P : Pl D.host.E) (k : ℕ) (α : GA D V) (z : (AE D)ˣ), ChrEq c χ → GlobalTheory.ExportSeries.UnramOutside c Q → GlobalTheory.ExportSeries.SplitSet Q → Bridge.SplitOff P (Q : Set (Pl D.host.E)) → IsHeckeAt V P k α → IsDetAt (idemAt P) V α z → ((c z : Circle) : ℂ) = ((χ.val P : ℂˣ) : ℂ) ^ k := by
  intro D c χ Q V P k α z hc hU hS hoff hα hz
  exact GlobalTheory.HeckeDetChar.chi_detAt hc hU hS hoff hα hz

end GlobalTheory.HeckeDetValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeReadOfReadsExist
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.IndefR.Lev (levG flag1L)
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}

section Delta

def IsDeltaInv (ρ : Setup D.ntw) (u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ) : Prop :=
  ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (P : PlE D.host), HkIdx i k P →
    ∀ (α : GA D (Wc D j)) (z : (AE D)ˣ), IsHeckeAt (Wc D j) P k α → IsDetAt (idemAt P) (Wc D j) α z →
      ρ.eO i b (u i b P) ^ k = (((ρ.B i j b).de.chi z : Circle) : ℂ)⁻¹

end Delta

section Pin

variable (Rl cG S) (YS : NX.NExpRealS Rl cG S)



end Pin

section Read

variable (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem evK_smul (c : NX.KB S i b) (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b (c • x) = ρ.e i b c • evK YS v₀ hρ i j b x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | tmul a f =>
    rw [TensorProduct.smul_tmul', evK_tmul, evK_tmul, smul_smul]
    exact congrArg (· • _) (map_mul (ρ.e i b) c a)

theorem evK_hkFR (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL ((j : ℕ) + 1)))
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) hL) (k : ℕ) (P : PlE D.host) (R : Finset (GA D (Wc D j))) (c : ℂ)
    (h : ∀ w, evW YS v₀ j (hL k P w) = c • fun x => ∑ γ ∈ R, evW YS v₀ j w (x * γ))
    (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b (NX.hkFR S i _ b hL hs k P t) = c • fun x => ∑ γ ∈ R, evK YS v₀ hρ i j b t (x * γ) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
    have e0 : NX.hkFR S i _ b hL hs k P ((x + y : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) : NX.Fm S i ((j : ℕ) + 1) b) =
        NX.hkFR S i _ b hL hs k P x + NX.hkFR S i _ b hL hs k P y := LinearMap.map_add _ _ _
    rw [e0]
    erw [map_add (evK YS v₀ hρ i j b)]
    rw [hx, hy, map_add (f := _), ← smul_add]
    congr 1
    funext x
    simp [Finset.sum_add_distrib]
  | tmul a f =>
    change evK YS v₀ hρ i j b (a ⊗ₜ[S.Ks] _) = _
    rw [evK_tmul, evK_tmul]
    change ρ.e i b a • evW YS v₀ j (hL k P f.1) = _
    rw [h]
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    ring

end Read

section Main

variable (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem heckeAt_of_scaled {ρ : Setup D.ntw} (hpin : RealPin Rl cG ρ) (hIs : Rl.toRealDat.toLevCh.Is A3.A.μ0)
    (hA : Rl.AllPlaces) (hρ : ρ.Good) {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    (hr : GlobalTheory.ExportPin.Reads Rl cG S YS hL) {u} (hδ : IsDeltaInv ρ u) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ)
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) (hL ((j : ℕ) + 1))) {k : ℕ} {P : PlE D.host} (hk : HkIdx i k P)
    {f g : D.nexp.Fm i ((j : ℕ) + 1) b}
    (e1 : YS.eF i _ b (Nat.le_add_left _ _) j.2 g = (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k •
      NX.hkFR S i _ b (hL _) hs k P (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) :
    HeckeAt (realRd YS v₀ hρ i j b ν) k P f g := by
  rintro α R z ⟨hα, hR, hz⟩
  funext x
  rw [Setup.hecke_apply]
  have hδ' := hδ i j b k P hk α z hα hz
  obtain ⟨hk1, hkr, hsp, hP⟩ := hk
  have ho : Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E)) := by
    have hprime : ∀ Q ∈ Rl.Sb, ∃ l, ((D.host.g l : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
      intro Q hQ
      rw [show Rl.Sb = Rl.Pg from hA] at hQ
      obtain ⟨l, hl⟩ := (hIs.Pg Q).1 hQ
      have hmem := Rl.C.P.pb_over l
      rw [← hl] at hmem
      have hcast : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g l : ℕ) : 𝓞 D.host.K) ∈ Q.asIdeal := hmem
      exact ⟨l, by rwa [map_natCast] at hcast⟩
    refine ⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hsp, ?_, ?_⟩
    · intro h
      obtain ⟨l, hl⟩ := hprime P h
      exact hP (D.ntw.placesOver_subset_exceptional i l hl)
    · intro Q hQ h
      obtain ⟨l, hl⟩ := hprime Q hQ
      rw [h, Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.mem_conjP, map_natCast] at hl
      exact hP (D.ntw.placesOver_subset_exceptional i l hl)
  have hR' : Bridge.IsDC (levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R :=
    GlobalTheory.PrincipalLevel.levK_eq_levG hpin i j b ▸ hR
  have hw : ∀ w, evW YS v₀ j (hL ((j : ℕ) + 1) k P w) =
      ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
        fun x => ∑ γ ∈ R, evW YS v₀ j w (x * γ) := by
    intro w
    have := hr j k P hsp ho hkr α R hα hR' w
    exact congrArg (fun T => T (v₀ j _)) this
  have hmu : (((ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k := by
    rw [hpin.mu0 i j b]
    refine GlobalTheory.HeckeDetChar.chi_detAt (hIs.mu0 j) (Q := Rl.Pg) ?_ ?_ ?_ hα hz
    · have := (hρ.base i j b).unram
      rwa [hpin.Pg i j b, hpin.mu0 i j b] at this
    · obtain ⟨Q, h1, -, h3⟩ := (hρ.base i j b).places.split
      exact hpin.Pg i j b ▸ h3.mono h1
    · have hA' : Rl.Sb = Rl.Pg := hA
      rw [← hA']; exact ho
  have hrk : (Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  change ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 g) x = _
  rw [e1]
  erw [evK_smul YS v₀ hρ i j b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k)]
  erw [evK_hkFR YS v₀ hρ i j b (hL ((j : ℕ) + 1)) hs k P R _ hw]
  have he : ρ.e i b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k) = ρ.eO i b (u i b P) ^ k := by
    rw [map_pow]; rfl
  have hm : (((ρ.B i j b).mu z : Circle) : ℂ) =
      (((ρ.B i j b).mu0 z : Circle) : ℂ) * (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
    rw [Base.mu, MonoidHom.mul_apply, Circle.coe_mul]
  have hr1 : ∀ y, realRd YS v₀ hρ i j b ν f y =
      ν⁻¹ * evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) y := fun _ => rfl
  have hq : normV P = Nat.card (Formalism.L2.DIV.kP P) := rfl
  simp only [hr1, Pi.smul_apply, smul_eq_mul, he, hδ', hm, hmu, hrk, hq]
  rw [← Finset.mul_sum]
  ring

end Main

end GlobalTheory.SeriesTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkSSOfSides
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwHkSS

theorem hkSS_of_sides : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), CommG D → HkComm D → SupFull D → HkSS D := by
  intro D X E Y hG hC hSF
  have hX : Formalism.IndefR.NX.NExpHeckeRowX X.R X.cG Y.S Y.YS Y.H (fun j => Formalism.IndefR.NX.goodProjW Y.S j D.nexp.eLL0) :=
    ⟨fun i k P hs ho _ _ hk α R hα hR x _ => Y.reads i k P hs ho hk α R hα hR x⟩
  exact GlobalTheory.GoodSpan.hkSS_of_rows_guarded X.R X.F X.cG Y.S Y.YS Y.H hG hC hSF hX X.char X.unif X.integral
    (fun i P P' hP hc => Y.Z.good.goodSetup_badPlaces_conj i P hP P' hc) (fun i => Y.Z.good.goodSetup_placesOverTwo_subset i) Y.Sb
    (fun i _ j hj b k P hk x => Y.hk_emb i j b k P x (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 hk)
    Y.B_range Y.hk_split

end GlobalTheory.TwHkSS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsFurther
section
namespace GlobalTheory.ScalarMultipleMembership

theorem exists_smul_mem {Ks WL : Type} [Field Ks] [NumberField Ks] [AddCommGroup WL] [Module Ks WL]
    [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL]
    (M : Submodule (NumberField.RingOfIntegers Ks) WL) (x : WL)
    (hx : x ∈ Submodule.span Ks (M : Set WL)) :
    ∃ a : NumberField.RingOfIntegers Ks, a ≠ 0 ∧ a • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem b hay
    · rw [mul_smul]; exact M.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨n, d, hd, hc⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers Ks) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap (NumberField.RingOfIntegers Ks) Ks d ≠ 0 := by
      intro h
      exact hd0 (IsFractionRing.injective (NumberField.RingOfIntegers Ks) Ks (by simpa using h))
    refine ⟨a * d, mul_ne_zero ha hd0, ?_⟩
    have key : (a * d) • c • y = n • a • y := by
      rw [← algebraMap_smul Ks (a * d), ← algebraMap_smul Ks n, ← algebraMap_smul Ks a,
        smul_smul, smul_smul, ← hc, map_mul]
      congr 1
      field_simp
    rw [key]
    exact M.smul_mem n hay

theorem main {LL Ks WL G : Type} [inst : Field LL] [NumberField LL] [inst_2 : Field Ks] [inst_3 : NumberField Ks] [inst_4 : Algebra Ks LL] [inst_5 : AddCommGroup WL] [inst_6 : Module LL WL] [inst_7 : Module Ks WL] [IsScalarTower Ks LL WL] [inst_9 : Module (NumberField.RingOfIntegers Ks) WL] [inst_10 : IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {W : (LL →+* ℂ) → Type} [inst_11 : (σ : LL →+* ℂ) → NormedAddCommGroup (W σ)] [inst_12 : (σ : LL →+* ℂ) → InnerProductSpace ℂ (W σ)] [inst_13 : Group G] (Φ : Formalism.IndefR.Arith.FormsL LL Ks WL W G)
    (h : Submodule.span Ks (↑(Formalism.IndefR.Arith.FormsL.MK Φ) : Set WL) = Formalism.IndefR.Arith.FormsL.WK Φ) :
    ∀ x ∈ Formalism.IndefR.Arith.FormsL.WK Φ, ∃ (a : NumberField.RingOfIntegers Ks), a ≠ (0 : NumberField.RingOfIntegers Ks) ∧ a • x ∈ Formalism.IndefR.Arith.FormsL.MK Φ := by
  intro x hx
  rw [← h] at hx
  exact exists_smul_mem _ x hx

end GlobalTheory.ScalarMultipleMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvPlaceNormProductMemCoefficientRing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormUnit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem coprime_absNorm {K : Type} [Field K] [NumberField K] (l : ℕ) (hl : l.Prime)
    (P : HeightOneSpectrum (𝓞 K)) (hP : ((l : ℕ) : 𝓞 K) ∉ P.asIdeal) :
    Nat.Coprime l (Ideal.absNorm P.asIdeal) := by
  rw [Nat.Prime.coprime_iff_not_dvd hl]
  intro hd
  haveI : Fact l.Prime := ⟨hl⟩
  letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  have hfin : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  haveI := Fintype.ofFinite (𝓞 K ⧸ P.asIdeal)
  have hc : l ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) := by
    rw [Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]; exact hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card l hc
  have h1 : (l : 𝓞 K ⧸ P.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [addOrderOf_zero] at hx; exact hl.one_lt.ne hx
  have h2 : (l : 𝓞 K ⧸ P.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  apply hP
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact h2

theorem isUnit_natCast_of_coprime {R : Type} [CommRing R] [IsLocalRing R] {l n : ℕ}
    (hl : ((l : ℕ) : R) ∈ IsLocalRing.maximalIdeal R) (h : Nat.Coprime l n) : IsUnit ((n : ℕ) : R) := by
  by_contra hn
  have hn' : ((n : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 h : IsCoprime (l : ℤ) (n : ℤ))
  have e : (1 : R) = (a : R) * (l : R) + (b : R) * (n : R) := by
    have := congrArg (Int.cast : ℤ → R) hab
    push_cast at this
    exact this.symm
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [e]; exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hn')
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem normProd_inv_mem (D : D7) (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) (Q : Finset (Pl D.host.E))
    (hQ : Disjoint Q (D.ntw.S0 i)) : ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eO i b).range := by
  have hcop : Nat.Coprime (D.ntw.l i) (normProd Q) := by
    unfold normProd
    refine Nat.Coprime.prod_right fun P hP => coprime_absNorm _ (D.ntw.lPrime i).out P fun hl => ?_
    exact Finset.disjoint_left.1 hQ hP (D.ntw.twistExcludedPlaces_contains_residueChar i hl)
  obtain ⟨u, hu⟩ := isUnit_natCast_of_coprime (D.ntw.O_l i) hcop
  refine ⟨(u⁻¹ : (D.ntw.O i)ˣ), ?_⟩
  have h1 : ρ.eO i b (u : D.ntw.O i) = ((normProd Q : ℕ) : ℂ) := by rw [hu, map_natCast]
  rw [← h1]
  exact map_units_inv (ρ.eO i b) u

end GlobalTheory.NormUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdemSumConjugatePlacesSubsetEqFlip
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.FlipIdemSum

open Formalism.L2.NTheta (IsIdemAt)

theorem idemSum_flip_subset : ∀ (D : D7) (e eT e' : AE D) (P T : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → IsIdemSum eT T → T ⊆ P → IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) → e' = e - eT + cA D eT := by
  intro D e eT e' P T he hT hTP he'
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  obtain ⟨⟨ts, hts, htsum⟩, -⟩ := hT
  obtain ⟨⟨gs, hgs, hgsum⟩, -⟩ := he'
  have hmul : ∀ Q ∈ P, e * es Q = es Q := fun Q hQ => by
    rw [hsum, Finset.sum_mul, Finset.sum_eq_single_of_mem Q hQ]
    · exact (hes Q hQ).1.1
    · intro R hR hne
      exact GlobalTheory.Tow.idemAt_orth (hes R hR) (hes Q hQ) hne
  have hconj : ∀ PP ∈ P, IsIdemAt (cA D (es PP)) (Formalism.L2.DIV.conjPl PP) := fun PP hPP =>
    GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun _ => Iff.rfl
  have hne : ∀ (a : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), IsIdemAt a Q → a ≠ 0 := by
    rintro a Q h rfl
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    have := (h.2 x hx0).1 hx
    rw [zero_mul, RingHom.map_zero] at this
    exact this (zero_mem _)
  have hdisj : Disjoint (P \ T) (T.image Formalism.L2.DIV.conjPl) := by
    rw [Finset.disjoint_left]
    intro Q hQ hQ'
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ'
    have hPPP := hTP hPP
    have h1 := hmul _ (Finset.mem_sdiff.1 hQ).1
    rw [GlobalTheory.Tow.idemAt_unique (hes _ (Finset.mem_sdiff.1 hQ).1) (hconj PP hPPP)] at h1
    have hea' : cA D e * cA D (es PP) = cA D (es PP) := by rw [← map_mul, hmul PP hPPP]
    exact hne _ _ (hconj PP hPPP)
      (by linear_combination (-1 : AE D) * h1 - e * hea' + cA D (es PP) * hc)
  have hinj : ∀ a ∈ T, ∀ b ∈ T, Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b → a = b := fun a _ b _ hab => by
    rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b]
  have hA : ∑ Q ∈ P \ T, gs Q = ∑ Q ∈ P \ T, es Q := Finset.sum_congr rfl fun Q hQ =>
    GlobalTheory.Tow.idemAt_unique (hgs Q (Finset.mem_union_left _ hQ)) (hes Q (Finset.mem_sdiff.1 hQ).1)
  have hB : ∑ Q ∈ T.image Formalism.L2.DIV.conjPl, gs Q = cA D eT := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_image hinj, htsum, map_sum]
    refine Finset.sum_congr rfl fun PP hPP => ?_
    rw [GlobalTheory.Tow.idemAt_unique (hts PP hPP) (hes PP (hTP hPP))]
    exact GlobalTheory.Tow.idemAt_unique (hgs _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))) (hconj PP (hTP hPP))
  have hTs : eT = ∑ Q ∈ T, es Q := by
    rw [htsum]
    exact Finset.sum_congr rfl fun PP hPP => GlobalTheory.Tow.idemAt_unique (hts PP hPP) (hes PP (hTP hPP))
  rw [hgsum, Finset.sum_union hdisj, hA, hB, hTs, hsum, ← Finset.sum_sdiff hTP]
  ring

end GlobalTheory.FlipIdemSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitCardResidueFieldOffExceptionalPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResidueUnit

theorem card_residueField_coprime {E : Type} [Field E] [NumberField E] (PP : Pl E) (l : ℕ) (hl : l.Prime)
    (hPP : ((l : ℕ) : 𝓞 E) ∉ PP.asIdeal) : Nat.Coprime (Nat.card (kP PP)) l := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  haveI : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot
  letI : Fintype (kP PP) := Fintype.ofFinite _
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (kP PP) (ringChar (kP PP))
  rw [Nat.card_eq_fintype_card, hcard]
  refine Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hl).2 ?_)
  intro hpl
  apply hPP
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : ((ringChar (kP PP) : ℕ) : kP PP) = 0 := ringChar.Nat.cast_ringChar
  rw [hpl] at h0
  simpa using h0

theorem natCast_mem_maximalIdeal_of_finite {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [IsLocalRing A] [Algebra O A] [Module.Finite O A] (l : ℕ) (hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) :
    ((l : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
  haveI : Algebra.IsIntegral O A := Algebra.IsIntegral.of_finite O A
  have hmax : ((IsLocalRing.maximalIdeal A).comap (algebraMap O A)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (IsLocalRing.maximalIdeal A)
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have : ((l : ℕ) : O) ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap O A) := heq ▸ hl
  simpa using this

theorem isUnit_of_coprime {A : Type} [CommRing A] [IsLocalRing A] (q l : ℕ) (h : Nat.Coprime q l)
    (hl : ((l : ℕ) : A) ∈ IsLocalRing.maximalIdeal A) : IsUnit ((q : ℕ) : A) := by
  have hc : IsCoprime ((q : ℤ)) ((l : ℤ)) := Nat.isCoprime_iff_coprime.2 h
  obtain ⟨a, b, hab⟩ := hc
  by_contra hq
  have hq' : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 hq
  apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a : A) * ((q : ℕ) : A) + (b : A) * ((l : ℕ) : A)) = 1 := by
    have := congrArg (Int.cast : ℤ → A) hab
    push_cast at this
    exact this
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq') (Ideal.mul_mem_left _ _ hl)

end GlobalTheory.ResidueUnit


open GlobalTheory.ResidueUnit in
theorem GlobalTheory.ResidueUnit.isUnit_card_residueField_Ok {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)
    (i : X.Tw) (k : ℕ) (PP : Pl D.host.E) :
    PP ∉ X.S0 i → IsUnit ((Nat.card (kP PP) : ℕ) : X.Ok i k) := by
  intro hP
  have hl : ((X.l i : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun h => hP (X.twistExcludedPlaces_contains_residueChar i h)
  haveI := X.Ok_fin i k
  exact isUnit_of_coprime _ _ (card_residueField_coprime PP (X.l i) (X.lPrime i).out hl)
    (natCast_mem_maximalIdeal_of_finite (O := X.O i) (X.l i) (X.O_l i))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalDatumSmallFieldFormHeckeScalarUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwUnit

theorem isKsForm_and_unit : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j, 1 ≤ j → j ≤ D.R.m → (Y.S.A j).IsKsForm) ∧ ∀ i b P, P ∉ D.ntw.S0 i → ∃ u : (D.ntw.O i)ˣ, Y.H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u := by
  intro D X E Y
  refine ⟨fun j h1 h2 => ?_, fun i b P hP => ?_⟩
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
    exact GlobalTheory.isKsForm_of_formsIso _ _ (Y.YS.fi ⟨n, h2⟩) (X.integral ⟨n, h2⟩).1
  · obtain ⟨σ, -, hσ⟩ := GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)
    exact ⟨Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom
      (if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹), Y.del i b P hP σ hσ⟩

end GlobalTheory.TwUnit
end

