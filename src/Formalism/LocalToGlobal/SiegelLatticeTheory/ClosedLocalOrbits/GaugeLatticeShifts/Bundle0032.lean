module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FormHermitianPositive
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0012

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLStmt
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.SatGramActL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LeftActC' : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    ∀ S ∈ ({(Y.tO u u').genSet, (Y.tO u u').ngSet, (Y.tO u u').degSet} :
      Set (Set (GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')))),
    Formalism.L2.SG.Pf.SatGram.LeftAct (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') S
      (Aset Y.TR (Y.cs u))

def kB {D : D7} {X : HidaSetting D} {w : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (c : ColSys X w rs) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (γ : Gam X w) : X.B.I.Gf :=
  ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w)⁻¹ * (iotaF X w γ : X.B.I.Gf) * ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w)

def kBB {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (x : X.B.I.GA) : X.B.I.Gf :=
  kOf X u u' ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) x

def BetaLift : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (w : D.what₂.Word) (rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (c : ColSys X w rs)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ rs → ∀ γ : Gam X w, kB c Λ γ ∈ X.B.I.Kset →
    ∃ β : (VS D).V ≃ₗ[D.host.E] (VS D).V, RatLink X (γ : X.B.I.GA) β ∧ β ∈ Saturated.AutF Λ (lf D (X.Fu w))

def SMemLeft : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t t' : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    β ∈ Saturated.AutF t.lam (lf D (X.Fu u)) → t'.lam = t.lam → t'.lam' = t.lam' →
    (∃ n ∈ NLam t.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t.lam' (lf D (X.Fu u')), t'.lin = n * (β * t.lin) * n') →
    ∀ S ∈ ({(Y.tO u u').genSet, (Y.tO u u').ngSet, (Y.tO u u').degSet} :
      Set (Set (GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')))), t ∈ S → t' ∈ S

def IotaLeft : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (γ : Gam X u), kB (Y.cs u) t.lam γ ∈ X.B.I.Kset →
      levi Y.TR (kB (Y.cs u) t.lam γ * kBB Y u u' t.lam t.lam' t.rep.1.1) =
        levi Y.TR (kB (Y.cs u) t.lam γ) * levi Y.TR (kBB Y u u' t.lam t.lam' t.rep.1.1)

def ChiNLeft : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    Λ ∈ Y.what₂ u → Λ' ∈ Y.what₂ u' → ∀ γ : Gam X u, kB (Y.cs u) Λ γ ∈ X.B.I.Kset →
    ∀ p : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ',
      chiN X (kB (Y.cs u) Λ γ * kBB Y u u' Λ Λ' p.1.1) = chiN X (kBB Y u u' Λ Λ' p.1.1)

def OOLeft : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (s : X.B.I.Ginf), s ∈ Hinf X u →
    ∀ (Ω : Set X.B.I.Ginf) (y : X.B.I.Ginf), MeasurableSet Ω →
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
       OO (Formalism.L2.SG.ProjRows.muInf X.B.I) ((fun x => s⁻¹ * x) ⁻¹' Ω) (X.Wu u) (X.Wu u') (s * y)) =
      (X.piU u s).comp (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') y)

def FundConj : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) (x0 : X.B.I.GA)
    (β γ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x0 β → β ∈ Saturated.AutF Λ (lf D (X.Fu u)) →
    ∀ Ω : Set X.B.I.Ginf, IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' γ) Ω →
      IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' (β * γ)) ((fun x => x0.1⁻¹ * x) ⁻¹' Ω)

section NC

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {Λ : Submodule (𝓞 E) S.V}
  {r : ℕ} {T : E} {F : LFlag S r T}

theorem fix_e {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F) (i : Fin r) : β (F.fl.e i) = F.fl.e i := by
  obtain ⟨-, hf, -⟩ := hβ
  have h := hf (Fin.castSucc i)
  unfold frame at h
  have hh : F.fl.fvec i.castSucc = F.fl.e i := by
    unfold FlagG.fvec
    simp
  exact hh ▸ h

theorem fix_xflag {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F) (j : ℕ) : ∀ x ∈ Xflag F j, β x = x := by
  intro x hx
  unfold Xflag FlagG.Xa at hx
  have hle : Submodule.span E (F.fl.e '' {i | ↑i < j}) ≤
      LinearMap.eqLocus (β : S.V →ₗ[E] S.V) LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨i, -, rfl⟩
    simpa [LinearMap.mem_eqLocus] using fix_e hβ i
  have h2 := hle hx
  simpa [LinearMap.mem_eqLocus] using h2

theorem fix_xsp {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F) : ∀ x ∈ Xsp F, β x = x := by
  intro x hx
  unfold Xsp FlagG.X at hx
  have hle : Submodule.span E (Set.range F.fl.e) ≤
      LinearMap.eqLocus (β : S.V →ₗ[E] S.V) LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simpa [LinearMap.mem_eqLocus] using fix_e hβ i
  have h2 := hle hx
  simpa [LinearMap.mem_eqLocus] using h2

theorem inv_fix {β : S.V ≃ₗ[E] S.V} {x : S.V} (h : β x = x) : β⁻¹ x = x := by
  calc β⁻¹ x = β⁻¹ (β x) := by rw [h]
    _ = x := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

theorem nlam_conj {β n : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F) (hn : n ∈ NLam Λ F) :
    β * n * β⁻¹ ∈ NLam Λ F := by
  unfold NLam at hn ⊢
  obtain ⟨hA, hF, hX⟩ := hn
  have hB := hβ
  unfold Saturated.AutF at hB
  obtain ⟨hBA, -, -⟩ := hB
  unfold IsAutLam at hA hBA
  obtain ⟨hAi, hAg⟩ := hA
  obtain ⟨hBi, hBg⟩ := hBA
  have hmap : ∀ (a b : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V),
      HermitianLatticesTheory.gmap (a * b) L = HermitianLatticesTheory.gmap a (HermitianLatticesTheory.gmap b L) := by
    intro a b L
    unfold HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    rfl
  have hone : ∀ L : Submodule (𝓞 E) S.V, HermitianLatticesTheory.gmap (1 : S.V ≃ₗ[E] S.V) L = L := by
    intro L
    unfold HermitianLatticesTheory.gmap
    have h1 : ((1 : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V).restrictScalars (𝓞 E) = LinearMap.id :=
      LinearMap.ext fun _ => rfl
    rw [h1, Submodule.map_id]
  have hBinv : HermitianLatticesTheory.gmap β⁻¹ Λ = Λ := by
    calc HermitianLatticesTheory.gmap β⁻¹ Λ = HermitianLatticesTheory.gmap β⁻¹ (HermitianLatticesTheory.gmap β Λ) := by rw [hBg]
      _ = Λ := by rw [← hmap, inv_mul_cancel, hone]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact mul_mem (mul_mem hBi hAi) (inv_mem hBi)
  · rw [hmap, hmap, hBinv, hAg, hBg]
  · intro j x hx
    have hx1 : β x = x := fix_xflag hβ (j + 1) x hx
    have hxi : β⁻¹ x = x := inv_fix hx1
    have hd := hF j x hx
    have hfix : β (n x - x) = n x - x := fix_xflag hβ j _ hd
    have hc : (β * n * β⁻¹) x - x = β (n x - x) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxi, map_sub, hx1]
    rw [hc, hfix]
    exact hd
  · intro x hx
    have hiso : ∀ a b, S.hT (β a) (β b) = S.hT a b := hBi
    have hxo : ∀ v ∈ Xsp F, S.hT v x = 0 := by
      intro v hv
      unfold orth at hx
      have h1 := (Submodule.mem_iInf _).1 hx v
      have h2 := (Submodule.mem_iInf _).1 h1 hv
      exact LinearMap.mem_ker.1 h2
    have hβy : β (β⁻¹ x) = x := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    have hy : β⁻¹ x ∈ orth S (Xsp F) := by
      unfold orth
      rw [Submodule.mem_iInf]
      intro v
      rw [Submodule.mem_iInf]
      intro hv
      rw [LinearMap.mem_ker]
      have hv' : β v = v := fix_xsp hβ v hv
      rw [← hiso v (β⁻¹ x), hv', hβy]
      exact hxo v hv
    have hd := hX (β⁻¹ x) hy
    have hfix : β (n (β⁻¹ x) - β⁻¹ x) = n (β⁻¹ x) - β⁻¹ x := fix_xsp hβ _ hd
    have hc : (β * n * β⁻¹) x - x = β (n (β⁻¹ x) - β⁻¹ x) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_sub, hβy]
    rw [hc, hfix]
    exact hd

end NC

end Formalism.L2.SG.Pf.SatGramActL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActR
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.NormCut Formalism.L2.SG.Pf.SatGramRep
  Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.SatGramActR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

def LiftAut : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (w : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ w → ∀ γ : Gam X w,
    ((((Y.cs w).h ((Y.cs w).base Λ) : X.B.I.Gf) * X.xu w)⁻¹ * (iotaF X w γ : X.B.I.Gf) *
        (((Y.cs w).h ((Y.cs w).base Λ) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset) →
    ∃ β : (VS D).V ≃ₗ[D.host.E] (VS D).V, RatLink X (γ : X.B.I.GA) β ∧
      β ∈ Formalism.L2.SG.Saturated.AutF Λ (lf D (X.Fu w))

def AutFConjN : Prop :=
  ∀ (D : D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V), β ∈ Formalism.L2.SG.Saturated.AutF Λ F →
    ∀ n ∈ NLam Λ F, β * n * β⁻¹ ∈ NLam Λ F

def ChiNR : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word) (h : Hfin X w) (γ : Gam X w) (κ : X.B.I.Gf),
    κ ∈ X.B.I.Kset →
    ((h : X.B.I.Gf) * X.xu w)⁻¹ * (iotaF X w γ : X.B.I.Gf) * ((h : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset →
    chiN X (κ * (((h : X.B.I.Gf) * X.xu w)⁻¹ * (iotaF X w γ : X.B.I.Gf) * ((h : X.B.I.Gf) * X.xu w))⁻¹) = chiN X κ

def OOR : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : Gam X u') (Ω : Set X.B.I.Ginf)
    (x : X.B.I.Ginf),
    (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
     OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') (x * ((γ : X.B.I.GA).1)⁻¹) =
       (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') x).comp (X.piU u' ((γ : X.B.I.GA).1)⁻¹))

end Steps

section Map

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem isom_of_autF {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ F) :
    β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  obtain ⟨⟨h1, -⟩, -, -⟩ := hβ
  exact h1

theorem gmap_of_autF {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ F) :
    Formalism.HermitianLatticesTheory.gmap β Λ = Λ := by
  obtain ⟨⟨-, h2⟩, -, -⟩ := hβ
  exact h2

theorem mapLF_mul_aut {Λ' : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' F)
    (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    mapLF (γ * β⁻¹) F = mapLF γ F := by
  have hiso := isom_of_autF hβ
  obtain ⟨-, hfr, hzt⟩ := hβ
  have hinv : ∀ v, β v = v → β⁻¹ v = v := by
    intro v hv
    calc β⁻¹ v = β⁻¹ (β v) := by rw [hv]
      _ = v := β.symm_apply_apply v
  have he : ∀ i, β (F.fl.e i) = F.fl.e i := by
    intro i
    have := hfr (Fin.castSucc i)
    simpa [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec] using this
  have hz : β F.fl.z = F.fl.z := by
    have := hfr (Fin.last _)
    simpa [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec] using this
  have key : ∀ A B : Formalism.MainNotions.S.FlagG (VS D) D.R.rS T, A.e = B.e → A.z = B.z → A = B := by
    rintro ⟨e1, z1, _, _, _, _⟩ ⟨e2, z2, _, _, _, _⟩ h1 h2
    cases h1
    cases h2
    rfl
  have hγβ : γ * β⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ hiso)
  unfold mapLF
  rw [dif_pos hγβ, dif_pos hγ]
  congr 1
  · apply key
    · funext a
      show γ (β⁻¹ (F.fl.e a)) = γ (F.fl.e a)
      rw [hinv _ (he a)]
    · show γ (β⁻¹ F.fl.z) = γ F.fl.z
      rw [hinv _ hz]
  · show γ (β⁻¹ F.zt) = γ F.zt
    rw [hinv _ hzt]

variable (x : X.B.I.GA) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)

def rmul (hx : RatLink X x β) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')) (p : GCar X u u' F0 F0' Λ Λ') : GCar X u u' F0 F0' Λ Λ' :=
  ⟨(p.1.1 * x⁻¹, p.1.2 * β⁻¹),
    Formalism.L2.SG.Pf.ratLink_mul X p.2.1 (Formalism.L2.SG.Pf.ratLink_inv X hx),
    Subgroup.mul_mem _ p.2.2.1 (Subgroup.inv_mem _ (isom_of_autF hβ)),
    by rw [Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_inv (gmap_of_autF hβ), p.2.2.2.1],
    (congrArg (TermDef.PD D Λ (lf D F0) u') (mapLF_mul_aut hβ p.1.2 p.2.2.1)).mpr p.2.2.2.2⟩

theorem rmul_rel (hN : AutFConjN) (hx : RatLink X x β) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')) (p q : GCar X u u' F0 F0' Λ Λ')
    (h : GRel X u u' F0 F0' Λ Λ' p q) : GRel X u u' F0 F0' Λ Λ' (rmul x β hx hβ p) (rmul x β hx hβ q) := by
  obtain ⟨n, hn, n', hn', hq⟩ := h
  refine ⟨n, hn, β * n' * β⁻¹, hN D Λ' (lf D F0') β hβ n' hn', ?_⟩
  show q.1.2 * β⁻¹ = n * (p.1.2 * β⁻¹) * (β * n' * β⁻¹)
  rw [hq]
  group

def cmap (hN : AutFConjN) (hx : RatLink X x β) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (c : GQ X u u' F0 F0' Λ Λ') : GQ X u u' F0 F0' Λ Λ' :=
  if hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0') then Quot.map (rmul x β hx hβ) (rmul_rel x β hN hx hβ) c else c

theorem cmap_pos (hN : AutFConjN) (hx : RatLink X x β) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')) (p : GCar X u u' F0 F0' Λ Λ') :
    cmap x β hN hx (Quot.mk _ p) = Quot.mk _ (rmul x β hx hβ p) := by
  unfold cmap
  exact dif_pos hβ

theorem cmap_neg (hN : AutFConjN) (hx : RatLink X x β) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hβ : β ∉ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')) (c : GQ X u u' F0 F0' Λ Λ') :
    cmap x β hN hx c = c := by
  unfold cmap
  exact dif_neg hβ

theorem cmap_inv (hN : AutFConjN) (hx : RatLink X x β) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (c : GQ X u u' F0 F0' Λ Λ') :
    cmap x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx) (cmap x β hN hx c) = c := by
  have inv_autF : ∀ {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V},
      γ ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0') → γ⁻¹ ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0') := by
    intro γ hγ
    have hiso := isom_of_autF hγ
    have hg := gmap_of_autF hγ
    obtain ⟨-, hfr, hzt⟩ := hγ
    have hinv : ∀ v, γ v = v → γ⁻¹ v = v := by
      intro v hv
      calc γ⁻¹ v = γ⁻¹ (γ v) := by rw [hv]
        _ = v := γ.symm_apply_apply v
    exact ⟨⟨Subgroup.inv_mem _ hiso, Formalism.L2.SG.Pf.gmap_inv hg⟩, fun a => hinv _ (hfr a), hinv _ hzt⟩
  by_cases hβ : β ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')
  · have hβ' := inv_autF hβ
    obtain ⟨p, rfl⟩ := Quot.exists_rep c
    rw [cmap_pos x β hN hx hβ p, cmap_pos x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx) hβ']
    congr 1
    apply Subtype.ext
    show ((p.1.1 * x⁻¹) * x⁻¹⁻¹, (p.1.2 * β⁻¹) * β⁻¹⁻¹) = p.1
    simp
  · have hβ' : β⁻¹ ∉ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0') := fun h => hβ (by simpa using inv_autF h)
    rw [cmap_neg x β hN hx hβ, cmap_neg x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx) hβ']

def tmap (hN : AutFConjN) (hx : RatLink X x β) (t : GTerm X u u' F0 F0' what₂ rows') : GTerm X u u' F0 F0' what₂ rows' :=
  ⟨t.lam, t.mem, t.lam', t.mem', cmap x β hN hx t.cls⟩

theorem tmap_inv (hN : AutFConjN) (hx : RatLink X x β) (t : GTerm X u u' F0 F0' what₂ rows') :
    tmap x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx) (tmap x β hN hx t) = t := by
  cases t
  simp only [tmap, cmap_inv]

def tequiv (hN : AutFConjN) (hx : RatLink X x β) : GTerm X u u' F0 F0' what₂ rows' ≃ GTerm X u u' F0 F0' what₂ rows' where
  toFun := tmap x β hN hx
  invFun := tmap x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx)
  left_inv t := tmap_inv x β hN hx t
  right_inv t := by
    have := tmap_inv x⁻¹ β⁻¹ hN (Formalism.L2.SG.Pf.ratLink_inv X hx) t
    simp only [inv_inv] at this
    exact this

theorem tmap_cls (hN : AutFConjN) (hx : RatLink X x β) (t : GTerm X u u' F0 F0' what₂ rows')
    (hβ : β ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D F0')) :
    (tmap x β hN hx t).cls = Quot.mk _ (rmul x β hx hβ t.rep) := by
  have h1 : t.cls = Quot.mk _ t.rep := (Quot.out_eq t.cls).symm
  show cmap x β hN hx t.cls = _
  rw [h1]
  exact cmap_pos x β hN hx hβ t.rep

theorem toTerm_tmap (hN : AutFConjN) (hx : RatLink X x β) (t : GTerm X u u' F0 F0' what₂ rows') :
    (tmap x β hN hx t).toTerm = t.toTerm := by
  by_cases hβ : β ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D F0')
  · have hTR := Formalism.L2.SG.Pf.toTermRel_holds X u u' F0 F0'
    have mk_congr : ∀ (A B : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
        (hA : TermDef.PD D t.lam (lf D F0) u' A) (hB : TermDef.PD D t.lam (lf D F0) u' B), A = B →
        TermDef.mk t.lam (lf D F0) (TermDef.PD D t.lam (lf D F0) u') ⟨A, hA⟩ =
          TermDef.mk t.lam (lf D F0) (TermDef.PD D t.lam (lf D F0) u') ⟨B, hB⟩ := by
      rintro A B hA hB rfl
      rfl
    let f : GCar X u u' F0 F0' t.lam t.lam' → TermDef.TermQ t.lam (lf D F0) (TermDef.PD D t.lam (lf D F0) u') :=
      fun p => TermDef.mk _ _ _ ⟨mapLF p.1.2 (lf D F0'), p.2.2.2.2⟩
    have hf : ∀ p q, GRel X u u' F0 F0' t.lam t.lam' p q → f p = f q := by
      intro p q h
      exact Quot.sound (hTR _ _ p q h)
    have key : ∀ c : GQ X u u' F0 F0' t.lam t.lam', f (Quot.out c) = Quot.lift f hf c :=
      fun c => congrArg (Quot.lift f hf) (Quot.out_eq c)
    have h1 := tmap_cls x β hN hx t hβ
    have h2 : f (tmap x β hN hx t).rep = f (rmul x β hx hβ t.rep) :=
      (key (tmap x β hN hx t).cls).trans (by rw [h1])
    have h3 : f (rmul x β hx hβ t.rep) = f t.rep :=
      mk_congr _ _ _ _ (mapLF_mul_aut hβ t.rep.1.2 t.rep.2.2.1)
    show (⟨t.lam, t.mem, f (tmap x β hN hx t).rep⟩ : TermDef.Term D u u' F0 what₂) = ⟨t.lam, t.mem, f t.rep⟩
    rw [h2, h3]
  · have h : tmap x β hN hx t = t := by
      show (⟨t.lam, t.mem, t.lam', t.mem', cmap x β hN hx t.cls⟩ : GTerm X u u' F0 F0' what₂ rows') = t
      rw [cmap_neg x β hN hx hβ]
    rw [h]

end Map

section Act

open Formalism.L2.SG.Full

def RightActC' : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    ∀ S ∈ ({(Y.tO u u').genSet, (Y.tO u u').ngSet, (Y.tO u u').degSet} :
      Set (Set (GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')))),
    Formalism.L2.SG.Pf.SatGram.RightAct (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') S
      (Aset Y.TR (Y.cs u'))

end Act

end Formalism.L2.SG.Pf.SatGramActR
end
end

